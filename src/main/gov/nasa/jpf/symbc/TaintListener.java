package gov.nasa.jpf.symbc;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.JVMInvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.JVMReturnInstruction;
import gov.nasa.jpf.jvm.bytecode.NATIVERETURN;
import gov.nasa.jpf.vm.NativeStackFrame;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.util.MethodSpec;
import gov.nasa.jpf.util.ObjectList;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ClassInfoException;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.NativeMethodInfo;
import gov.nasa.jpf.vm.NativePeer;
import gov.nasa.jpf.vm.SkippedMethodInfo;
import gov.nasa.jpf.vm.SkippedNativeMethodInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.Types;
import gov.nasa.jpf.vm.VM;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Taint listener for SPF.
 *
 * Strategy:
 *  1. classLoaded: replace unhandled native methods in *app* classes with
 *     SkippedNativeMethodInfo so they return 0/null instead of throwing.
 *  2. instructionExecuted / JVMReturnInstruction: when ANY source method
 *     (native or Java) returns, attach a TaintTag to the return value on the
 *     caller's stack and to the heap object if the return type is a reference.
 *     NATIVERETURN extends JVMReturnInstruction so both cases are handled here.
 *  3. executeInstruction / invoke: if a sink argument carries TaintTag on the
 *     operand/local path or heap object, report a taint flow.
 *
 * Framework classes (android.*, java.*, …) are intentionally left alone so
 * JPF throws UnsatisfiedLinkError for truly unresolvable natives — that stops
 * the search quickly without infinite-looping on class initializers.
 */
public class TaintListener extends PropertyListenerAdapter {

    private static String[] skip_spec   = null;
    private static boolean  initialized = false;
    private static ArrayList<String> sources = null;
    private static ArrayList<String> sinks   = null;
    private static boolean traceEnabled = true;
    private static String traceFile = "taint_trace.log";

    private final ArrayList<String> traceLines = new ArrayList<>();

    // ── bytecode-level dataflow propagation ───────────────────────────────────
    //
    // JPF's StackFrame already propagates operand attrs for: local loads/stores
    // (pushLocal/storeOperand copy attrs), field reads (GETFIELD/GETSTATIC set
    // operand attr from field attr), field writes (PutHelper copies operand attr
    // to field attr), array loads/stores (ArrayLoadInstruction/AASTORE explicitly
    // set element attrs), DUP variants, SWAP, and return instructions.
    //
    // The following instruction categories destroy operand attrs before pushing
    // the result and therefore require explicit pre/post propagation:
    //   arithmetic, bitwise, shift, type conversions, comparisons, unary negation.

    // Binary ops: two 1-slot inputs → one 1-slot result
    private static final Set<String> BIN_INT = new HashSet<>(Arrays.asList(
        "iadd","isub","imul","idiv","irem","ior","iand","ixor","ishl","ishr","iushr"
    ));
    // Binary ops: two 1-slot float inputs → one 1-slot result  (includes compare → int)
    private static final Set<String> BIN_FLOAT = new HashSet<>(Arrays.asList(
        "fadd","fsub","fmul","fdiv","frem","fcmpg","fcmpl"
    ));
    // Binary ops: two 2-slot long inputs → 2-slot (ladd…) or 1-slot (lcmp) result
    private static final Set<String> BIN_LONG = new HashSet<>(Arrays.asList(
        "ladd","lsub","lmul","ldiv","lrem","lor","land","lxor","lcmp"
    ));
    // Binary ops: two 2-slot double inputs → 2-slot (dadd…) or 1-slot (dcmpg/dcmpl) result
    private static final Set<String> BIN_DOUBLE = new HashSet<>(Arrays.asList(
        "dadd","dsub","dmul","ddiv","drem","dcmpg","dcmpl"
    ));
    // Shift ops: 2-slot long + 1-slot int → 2-slot long
    private static final Set<String> LONG_SHIFT = new HashSet<>(Arrays.asList(
        "lshl","lshr","lushr"
    ));
    // Unary ops: one 1-slot → one 1-slot
    private static final Set<String> UNARY_INT = new HashSet<>(Arrays.asList("ineg","fneg"));
    // Unary ops: one 2-slot → one 2-slot
    private static final Set<String> UNARY_LONG = new HashSet<>(Arrays.asList("lneg","dneg"));
    // Type conversions from a 1-slot int/float input
    private static final Set<String> CONV_FROM1 = new HashSet<>(Arrays.asList(
        "i2l","i2f","i2d","i2b","i2c","i2s","f2i","f2l","f2d"
    ));
    // Type conversions from a 2-slot long/double input
    private static final Set<String> CONV_FROM2 = new HashSet<>(Arrays.asList(
        "l2i","l2f","l2d","d2i","d2l","d2f"
    ));
    // Mnemonics whose result occupies 2 slots (long or double); all others produce 1 slot
    private static final Set<String> TWO_SLOT_RESULT = new HashSet<>(Arrays.asList(
        "ladd","lsub","lmul","ldiv","lrem","lor","land","lxor",
        "lshl","lshr","lushr","lneg",
        "dadd","dsub","dmul","ddiv","drem","dneg",
        "i2l","i2d","f2l","f2d","l2d","d2l",
        "laload","daload"
    ));

    // Array-load ops: stack before is ..., arrayref, index (index on top, 1 slot).
    // A tainted INDEX means the loaded value depends on which element was picked
    // (a table-lookup implicit flow, e.g. lookup[secretChar]) even when the
    // array's own contents are untainted constants. JPF's built-in array-load
    // semantics already copy any element-level attr onto the result; this set
    // additionally taints the result when the *index* itself is tainted.
    private static final Set<String> ARRAY_LOAD_OPS = new HashSet<>(Arrays.asList(
        "iaload","laload","faload","daload","aaload","baload","caload","saload"
    ));

    // Java library methods that propagate taint from any argument to the return value.
    // Covers string manipulation, encoding, collection read-back, and byte conversion.
    private static final Set<String> TAINT_THROUGH = new HashSet<>(Arrays.asList(
        "append", "toString", "concat", "valueOf", "format",
        "substring", "trim", "toLowerCase", "toUpperCase",
        "replace", "replaceAll", "replaceFirst", "intern",
        "strip", "stripLeading", "stripTrailing",
        "getBytes", "toCharArray", "getChars", "encode", "decode",
        "wrap", "copyOf", "copyOfRange", "join", "split",
        "get", "put", "add", "set",
        // String.equals()/equalsIgnoreCase(): taints the boolean result so a
        // later branch on it is recognized as a tainted (implicit-flow) condition.
        "equals", "equalsIgnoreCase",
        // java.util.regex: taint on the input CharSequence propagates to the Matcher
        // and from the Matcher to any group() / replaceAll() result.
        "matcher", "group", "replaceFirst", "appendReplacement", "appendTail",
        // ProcessBuilder.command(String...) returns `this`, so tagging the return
        // value (via applyReturnTaint) taints the receiver itself.
        "command"
    ));

    // Branch instructions that consume tainted values as conditions → implicit flow.
    private static final Set<String> BRANCH_OPS = new HashSet<>(Arrays.asList(
        "ifeq","ifne","iflt","ifge","ifgt","ifle",
        "if_icmpeq","if_icmpne","if_icmplt","if_icmpge","if_icmpgt","if_icmple",
        "if_acmpeq","if_acmpne","ifnull","ifnonnull",
        "tableswitch","lookupswitch"
    ));

    // Taint captured from pre-execution operands; applied to the result post-execution.
    // Safe as plain fields because JPF executes instructions serially from one thread.
    private TaintTag pendingPropag      = null;  // arithmetic / conversion ops
    private TaintTag pendingInvokeTaint = null;  // taint-through library calls
    private TaintTag pendingBranchTaint = null;  // implicit flow via branch condition

    // Pending side-effect tagging for void TAINT_THROUGH methods (e.g. getChars, format).
    // Arg refs are captured pre-exec; tainting is applied post-exec in instructionExecuted.
    private TaintTag pendingVoidTag        = null;
    private int[]    pendingVoidArgRefs    = null;
    private boolean[] pendingVoidArgIsRef  = null;

    // ── native taint handoff (SPF→Kharon bridge) ───────────────────────────────
    //
    // When SPF detects taint reaching a native app method, it records per-argument
    // taint detail here.  On searchFinished the records are serialised to
    // taint.handoff.file so Kharon can initialize the right symbolic variables
    // as tainted before running angr symbolic execution on the native body.

    private static String handoffFile = null;

    // Native methods whose taint-through behaviour was determined by Kharon.
    // Loaded from taint.native_through config (comma-separated method specs).
    // When a call to one of these methods carries tainted args, taint is
    // propagated to the return value exactly like a Java TAINT_THROUGH method.
    private static ArrayList<String> nativeTaintThrough = null;

    // Native methods Kharon symbolically executed and found to leak a tainted
    // argument into an exfiltration API inside the .so.  Loaded from
    // taint.native_sinks.
    private static ArrayList<String> nativeConfirmedSinks = null;

    // Native methods Kharon symbolically executed at all, whatever the verdict
    // (taint.native_analyzed).  Only these are subject to confirmation: a
    // native method Kharon never looked at keeps the name-based verdict rather
    // than being silently cleared.
    private static ArrayList<String> nativeAnalyzed = null;

    // When set (taint.require_confirmed_native_sinks), an app-declared native
    // method that Kharon analysed is a sink only if Kharon confirmed it.
    // Java-side name matching cannot distinguish a native method that leaks its
    // argument from one that ignores it — both look like a tainted value
    // flowing into a method called "send" — so without native evidence the
    // name match alone produces false positives.
    private static boolean requireConfirmedNativeSinks = false;

    // ── native effects (Kharon → SPF, "what the native body did") ────────────
    //
    // SPF never executes a native body, so any state change it makes is invisible
    // and, worse, absent: after `Foo f = setField(c)` both `f` and `c.foo` are
    // still null, and the Java code NPEs on `f.getData()` before reaching its
    // sink.  A native effect declares one such change so SPF can replay it:
    // materialise the objects the native code would have created and mark the
    // written value tainted (or clean, which models a native sanitiser).
    //
    // Config format — taint.native_effects, comma-separated:
    //     <signature>|<target>|<fieldPath>|<tainted>|<sourceApi>|<aliasArg>
    //   signature  full JVM signature, e.g. org.x.A.setField(Lorg/x/C;)Lorg/x/F;
    //   target     "return" or "argN" (N = index into the Java arg list)
    //   fieldPath  dotted path from the target, may be empty for the target itself
    //   tainted    1 = write tainted data, 0 = write clean data (sanitiser)
    //   sourceApi  origin to attribute the taint to, for reporting
    //   aliasPath  "argM" or "argM.f…": copy the object at this path into the
    //              target instead of a fresh taint (the native aliased an
    //              argument or one of its fields); empty if none
    private static ArrayList<NativeEffect> nativeEffects = null;

    private static final class NativeEffect {
        final String  signature;
        final String  target;      // "return" | "argN"
        final String  fieldPath;   // "" | "data" | "foo.data"
        final boolean tainted;
        final String  sourceApi;
        final String  aliasPath;   // "" = none, else "argM[.f…]"

        NativeEffect(String signature, String target, String fieldPath,
                     boolean tainted, String sourceApi, String aliasPath) {
            this.signature = signature;
            this.target    = target;
            this.fieldPath = fieldPath;
            this.tainted   = tainted;
            this.sourceApi = sourceApi;
            this.aliasPath = aliasPath;
        }
    }

    // Arg refs captured pre-invoke so effects can be applied once the native
    // call returns (by then the arguments have been popped off the stack).
    private MethodInfo pendingEffectMethod  = null;
    private int[]      pendingEffectArgRefs = null;

    private static final class HandoffArg {
        final int    javaArgIndex;   // index in getArgumentValues() — 0 = receiver for virtual
        final int    jniParamIndex;  // index in JNI C signature — 0=env, 1=this/jclass, 2+=params
        final String javaType;       // e.g. "java.lang.String", "byte[]"
        final String jniType;        // e.g. "jstring", "jbyteArray", "jint"
        final String taintSource;    // TaintTag.source  (matches source spec, e.g. "getDeviceId")
        final String taintOrigin;    // TaintTag.origin  (full method FQN)
        // For array args: indices whose element carries the taint.  null when
        // the argument is not an array or taint sits on the object itself.
        final ArrayList<Integer> taintedElements;

        HandoffArg(int javaArgIndex, int jniParamIndex,
                   String javaType, String jniType,
                   String taintSource, String taintOrigin,
                   ArrayList<Integer> taintedElements) {
            this.javaArgIndex  = javaArgIndex;
            this.jniParamIndex = jniParamIndex;
            this.javaType      = javaType;
            this.jniType       = jniType;
            this.taintSource   = taintSource;
            this.taintOrigin   = taintOrigin;
            this.taintedElements = taintedElements;
        }
    }

    private static final class HandoffEntry {
        final String           nativeFqn;
        final boolean          isStatic;
        final Set<String>      callerEntrypoints = new LinkedHashSet<>();
        final List<HandoffArg> taintedArgs       = new ArrayList<>();

        HandoffEntry(String nativeFqn, boolean isStatic) {
            this.nativeFqn = nativeFqn;
            this.isStatic  = isStatic;
        }
    }

    // keyed by native FQN — accumulated across all symbolic paths
    private final Map<String, HandoffEntry> nativeHandoffs = new LinkedHashMap<>();

    // ── taint helpers ─────────────────────────────────────────────────────────

    private static TaintTag firstTaint(Object attrs) {
        return ObjectList.getFirst(attrs, TaintTag.class);
    }

    private static boolean hasTaint(ElementInfo ei) {
        return firstTaint(ei) != null;
    }

    private static TaintTag firstTaint(ElementInfo ei) {
        return ei == null ? null : ei.getObjectAttr(TaintTag.class);
    }

    private static void addTaint(ElementInfo ei, TaintTag tag) {
        if (ei == null || tag == null) return;
        if (ei.getObjectAttr(TaintTag.class) == null) {
            ei.addObjectAttr(tag);
        }
        // Arrays carry taint as a single object attr (e.g. from a tainted
        // String.toCharArray()/getChars() return), but reading an element via
        // *ALOAD only inherits a per-element attr (JPF's built-in array-load
        // semantics), not the array's object attr. Tag every element too so
        // those reads see the taint.
        if (ei.isArray()) {
            int len = ei.arrayLength();
            for (int i = 0; i < len; i++) {
                if (ei.getElementAttr(i, TaintTag.class) == null) {
                    ei.addElementAttr(i, tag);
                }
            }
        }
    }

    /** Taint via ref — uses getModifiable so it is safe to call in pre-exec (executeInstruction). */
    private static void addTaintRef(ThreadInfo ti, int ref, TaintTag tag) {
        if (ref == MJIEnv.NULL || tag == null) return;
        ElementInfo ei = ti.getHeap().getModifiable(ref);
        if (ei != null && ei.getObjectAttr(TaintTag.class) == null) {
            ei.addObjectAttr(tag);
        }
    }

    private static boolean hasTaint(StackFrame f) {
        return firstTaint(f) != null;
    }

    private static TaintTag firstTaint(StackFrame f) {
        return f == null ? null : f.getFrameAttr(TaintTag.class);
    }

    private static void addTaint(StackFrame f, TaintTag tag) {
        if (f != null && tag != null && f.getFrameAttr(TaintTag.class) == null) {
            f.addFrameAttr(tag);
        }
    }

    private static Object addTaintAttr(Object attrs, TaintTag tag) {
        if (tag == null || firstTaint(attrs) != null) {
            return attrs;
        }
        return ObjectList.add(attrs, tag);
    }

    private static boolean matchesAny(MethodInfo mi, ArrayList<String> specs) {
        String methodName = mi.getBaseName();
        String fullName = mi.getFullName();
        for (String spec : specs) {
            if (spec.indexOf('.') >= 0) {
                if (fullName.contains(spec)) return true;
            } else if (methodName.contains(spec)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Match a method against Kharon's native-method specs.
     *
     * Unlike {@link #matchesAny}, a spec carrying a descriptor must match the
     * method's full signature exactly.  Overloads share a name, so a substring
     * match on "MainActivity.send" would let a verdict about send(int) decide
     * the fate of send(String) — for suppression that would silently drop a
     * real leak in an overload Kharon never looked at.
     */
    private static boolean matchesNativeSpec(MethodInfo mi, ArrayList<String> specs) {
        if (specs == null || specs.isEmpty()) return false;
        String fullName = mi.getFullName();
        for (String spec : specs) {
            if (spec.indexOf('(') >= 0) {
                if (fullName.equals(spec)) return true;
            } else if (fullName.contains(spec)) {
                return true;
            }
        }
        return false;
    }

    private static String matchingSpec(MethodInfo mi, ArrayList<String> specs) {
        String methodName = mi.getBaseName();
        String fullName = mi.getFullName();
        for (String spec : specs) {
            if (spec.indexOf('.') >= 0) {
                if (fullName.contains(spec)) return spec;
            } else if (methodName.contains(spec)) {
                return spec;
            }
        }
        return null;
    }

    // ── init ──────────────────────────────────────────────────────────────────

    private void init(Config conf) {
        if (initialized) return;
        initialized = true;
        skip_spec = conf.getStringArray("nhandler.spec.skip");
        traceEnabled = conf.getBoolean("taint.trace", true);
        traceFile = conf.getString("taint.trace.file", "taint_trace.log");
        sources = defaultList(conf, "taint.sources",
            "getDeviceId", "getImei", "getLine1Number", "getSubscriberId",
            "getSimSerialNumber", "getNetworkOperator", "getNetworkCountryIso",
            "getSimCountryIso", "getMacAddress", "getAddress",
            "getLatitude", "getLongitude", "getLastKnownLocation", "getLastLocation");
        sinks = defaultList(conf, "taint.sinks",
            "send", "exec", "connect", "write", "println",
            "android.util.Log",
            "sendTextMessage", "sendDataMessage", "openConnection",
            // dot-qualified so it doesn't over-match unrelated "start" methods
            // (Thread.start, Service lifecycle, etc.)
            "ProcessBuilder.start");
        handoffFile = conf.getString("taint.handoff.file", null);

        nativeTaintThrough   = trimmedList(conf, "taint.native_through");
        nativeConfirmedSinks = trimmedList(conf, "taint.native_sinks");
        nativeAnalyzed       = trimmedList(conf, "taint.native_analyzed");
        requireConfirmedNativeSinks =
            conf.getBoolean("taint.require_confirmed_native_sinks", false);

        nativeEffects = new ArrayList<>();
        for (String spec : trimmedList(conf, "taint.native_effects")) {
            String[] p = spec.split("\\|", -1);
            if (p.length < 4) {
                System.out.println("[TaintListener] ignoring malformed taint.native_effects entry: " + spec);
                continue;
            }
            String aliasPath = p.length > 5 ? p[5].trim() : "";
            nativeEffects.add(new NativeEffect(
                p[0].trim(), p[1].trim(), p[2].trim(),
                !"0".equals(p[3].trim()),
                p.length > 4 ? p[4].trim() : "native",
                aliasPath));
        }
        if (!nativeEffects.isEmpty()) {
            System.out.println("[TaintListener] " + nativeEffects.size()
                + " native effect(s) loaded from Kharon");
        }
    }

    /**
     * Read a config list of specs that may carry JVM descriptors.
     *
     * JPF's Config splits list values on ',' AND ';' (Config.DELIMS), so a JVM
     * descriptor like "(Ljava/lang/String;)V" would be torn into fragments and
     * any signature match against it would be meaningless — or worse, a stray
     * fragment such as ")V" would substring-match every void method. The writer
     * (SPFRunner._esc_descriptors) escapes each ';' with JPF's own backtick
     * quote; Config.split consumes the backtick and hands us a clean ';', so
     * nothing needs undoing here beyond trimming.
     */
    private static ArrayList<String> trimmedList(Config conf, String key) {
        ArrayList<String> list = new ArrayList<>();
        String[] vals = conf.getStringArray(key);
        if (vals != null) {
            for (String v : vals) {
                String t = v.trim();
                if (!t.isEmpty()) list.add(t);
            }
        }
        return list;
    }

    private static ArrayList<String> defaultList(Config conf, String key, String... defs) {
        String[] vals = conf.getStringArray(key);
        ArrayList<String> list = new ArrayList<>();
        if (vals != null && vals.length > 0) {
            for (String v : vals) list.add(v.trim());
        } else {
            for (String v : defs) list.add(v);
        }
        return list;
    }

    // ── class loading ─────────────────────────────────────────────────────────

    // Framework classes whose unresolvable natives we stub out so class
    // initializers can complete without UnsatisfiedLinkError.
    private static final String[] FRAMEWORK_STUBS = {
        "android.util.Log",
        "android.os.SystemProperties",
        "android.os.StrictMode",
        "android.os.Handler",
        "android.os.MessageQueue",
        "android.os.Looper",
        "android.os.Process",
        "android.os.Build",
        "android.os.Environment",
        "android.os.Binder",
        "android.os.IBinder",
        "android.app.ActivityThread",
        "android.app.AppGlobals",
        "android.content.res.AssetManager",
        "android.content.res.Resources",
        "android.telephony.TelephonyManager",
        "android.location.Location",
        "libcore.io.OsConstants",
        "libcore.io.Posix",
        "libcore.icu.NativeConverter",
        "libcore.icu.ICU",
        "libcore.icu.LocaleData",
        "dalvik.system.VMRuntime",
        "dalvik.system.VMStack",
        "dalvik.system.CloseGuard",
        "java.util.TimeZone",
        "java.util.Date",
        "java.util.concurrent.atomic.AtomicLong",
    };

    @Override
    public void classLoaded(VM vm, ClassInfo ci) {
        init(vm.getConfig());
        String name = ci.getName();
        if (!isFrameworkClass(name) || isFrameworkStub(name)) {
            skipNativesInClass(ci);
        }
        processSkipped(ci);
    }

    private static boolean isFrameworkClass(String name) {
        return name.startsWith("android.") || name.startsWith("java.")
            || name.startsWith("javax.")   || name.startsWith("sun.")
            || name.startsWith("com.android.") || name.startsWith("dalvik.")
            || name.startsWith("libcore.")  || name.startsWith("gov.nasa.jpf.");
    }

    private static boolean isFrameworkStub(String name) {
        for (String s : FRAMEWORK_STUBS) if (name.startsWith(s)) return true;
        return false;
    }

    private void skipNativesInClass(ClassInfo ci) {
        for (MethodInfo mi : ci.getDeclaredMethodInfos()) {
            if (mi.isNative() && !isHandled(mi)) {
                ci.putDeclaredMethod(new SkippedNativeMethodInfo(mi));
            }
        }
    }

    private static boolean isHandled(MethodInfo mi) {
        NativeMethodInfo nmi = (NativeMethodInfo) mi;
        NativePeer peer = nmi.getNativePeer();
        if (peer == null) return false;
        String jniName = nmi.getJNIName();
        for (Method m : peer.getPeerClass().getMethods()) {
            if (m.getName().equals(jniName) || jniName.contains(m.getName())) return true;
        }
        return false;
    }

    private void processSkipped(ClassInfo ci) {
        if (skip_spec == null) return;
        for (MethodInfo mi : ci.getDeclaredMethodInfos()) {
            for (String spec : skip_spec) {
                if (MethodSpec.createMethodSpec(spec).matches(mi)) {
                    ci.putDeclaredMethod(new SkippedMethodInfo(mi));
                }
            }
        }
    }

    // ── taint tracking ────────────────────────────────────────────────────────

    @Override
    public void executeInstruction(VM vm, ThreadInfo ti, Instruction insn) {
        pendingPropag      = null;
        pendingInvokeTaint = null;
        pendingBranchTaint = null;
        pendingVoidTag     = null;
        pendingVoidArgRefs = null;
        pendingVoidArgIsRef = null;
        if (insn instanceof JVMInvokeInstruction) {
            handleInvoke(ti, (JVMInvokeInstruction) insn);
            pendingInvokeTaint = captureInvokeTaint(ti, (JVMInvokeInstruction) insn);
        } else {
            pendingPropag      = captureArithmeticTaint(ti, insn);
            pendingBranchTaint = captureBranchTaint(ti, insn);
        }
    }

    @Override
    public void instructionExecuted(VM vm, ThreadInfo ti,
                                    Instruction next, Instruction insn) {
        if (pendingPropag != null) {
            applyArithmeticTaint(ti, insn, pendingPropag);
            pendingPropag = null;
        }
        if (pendingInvokeTaint != null) {
            applyInvokeTaint(ti, insn, pendingInvokeTaint);
            pendingInvokeTaint = null;
        }
        if (pendingBranchTaint != null) {
            propagateImplicitTaint(ti, pendingBranchTaint);
            pendingBranchTaint = null;
        }
        // Apply deferred tainting of reference-type args for void TAINT_THROUGH methods.
        // Called post-exec so addObjectAttr runs when the heap is modifiable.
        if (pendingVoidTag != null && pendingVoidArgRefs != null) {
            for (int i = 0; i < pendingVoidArgRefs.length; i++) {
                if (pendingVoidArgIsRef[i]) {
                    addTaint(ti.getHeap().get(pendingVoidArgRefs[i]), pendingVoidTag);
                }
            }
            pendingVoidTag     = null;
            pendingVoidArgRefs = null;
            pendingVoidArgIsRef = null;
        }
        if (insn instanceof JVMReturnInstruction) {
            // Effects first: a native source materialises its return value here,
            // and handleSourceReturn/applyReturnTaint then see a real object.
            applyNativeEffects(ti, (JVMReturnInstruction) insn);
            handleSourceReturn(ti, (JVMReturnInstruction) insn);
            applyReturnTaint(ti, (JVMReturnInstruction) insn);
        }
        recordInstructionTaint(ti, insn);
    }

    @Override
    public void searchFinished(Search search) {
        if (traceEnabled && !traceLines.isEmpty()) {
            File out = new File(traceFile);
            try {
                File parent = out.getParentFile();
                if (parent != null) parent.mkdirs();

                FileWriter writer = new FileWriter(out);
                try {
                    for (String line : traceLines) {
                        writer.write(line);
                        writer.write(System.lineSeparator());
                    }
                } finally {
                    writer.close();
                }
                System.out.println("[TaintListener] instruction trace written: " + out.getPath());
            } catch (IOException ioe) {
                System.out.println("[TaintListener] failed to write instruction trace: " + ioe);
            }
        }
        writeHandoffJson();
    }

    private void trace(String line) {
        if (traceEnabled) {
            traceLines.add(line);
        }
    }

    private void recordInstructionTaint(ThreadInfo ti, Instruction insn) {
        if (!traceEnabled || insn == null) return;

        StackFrame frame = ti.getTopFrame();
        if (frame == null) return;

        Set<TaintTag> tags = new LinkedHashSet<TaintTag>();
        StringBuilder where = new StringBuilder();

        TaintTag frameTag = firstTaint(frame);
        if (frameTag != null) {
            tags.add(frameTag);
            where.append(" frame");
        }

        int nLocals = frame.getLocalVariableCount();
        for (int i = 0; i < nLocals; i++) {
            TaintTag tag = firstTaint(frame.getLocalAttr(i));
            if (tag == null && frame.isLocalVariableRef(i)) {
                tag = firstTaint(ti.getHeap().get(frame.getLocalVariable(i)));
            }
            if (tag != null) {
                tags.add(tag);
                where.append(" L").append(i);
            }
        }

        int top = frame.getTopPos();
        int nOperands = top >= nLocals ? top - nLocals + 1 : 0;
        for (int off = 0; off < nOperands; off++) {
            TaintTag tag = firstTaint(frame.getOperandAttr(off));
            if (tag == null && frame.isOperandRef(off)) {
                tag = firstTaint(ti.getHeap().get(frame.peek(off)));
            }
            if (tag != null) {
                tags.add(tag);
                where.append(" S").append(off);
            }
        }

        if (!tags.isEmpty()) {
            trace("[TaintTrace] "
                + insn.getMethodInfo().getFullName()
                + " @"
                + insn.getPosition()
                + " "
                + insn
                + " | at:"
                + where.toString()
                + " | tags="
                + tags.toString());
        }
    }

    // ── bytecode-level dataflow propagation ───────────────────────────────────

    /**
     * Inspect the operand stack BEFORE the instruction executes and return the
     * first TaintTag found among the instruction's input operands.  Returns null
     * when none of the inputs are tainted, or when the instruction is not an
     * arithmetic / conversion / comparison op that needs explicit propagation.
     *
     * Called from executeInstruction (pre-exec) and stored in pendingPropag.
     */
    private TaintTag captureArithmeticTaint(ThreadInfo ti, Instruction insn) {
        StackFrame frame = ti.getTopFrame();
        if (frame == null) return null;

        String m = insn.getMnemonic();

        // ── binary ops with two 1-slot inputs ────────────────────────────────
        if (BIN_INT.contains(m) || BIN_FLOAT.contains(m)) {
            TaintTag t0 = taintAtSlot(ti, frame, 0);
            TaintTag t1 = taintAtSlot(ti, frame, 1);
            return t0 != null ? t0 : t1;
        }

        // ── binary ops with two 2-slot inputs ────────────────────────────────
        // Stack layout before: ..., [A_hi @ top-3, A_lo @ top-2], [B_hi @ top-1, B_lo @ top]
        // Long/double attrs are stored at the high-word slot (offset 1 for B, offset 3 for A).
        if (BIN_LONG.contains(m) || BIN_DOUBLE.contains(m)) {
            TaintTag t0 = taintAtSlot(ti, frame, 1); // B high word
            TaintTag t1 = taintAtSlot(ti, frame, 3); // A high word
            return t0 != null ? t0 : t1;
        }

        // ── shift: long (2-slot) shifted by int (1-slot) ─────────────────────
        // Stack: ..., [long_hi @ top-2, long_lo @ top-1], [int @ top]
        if (LONG_SHIFT.contains(m)) {
            TaintTag t0 = taintAtSlot(ti, frame, 0); // int shift amount
            TaintTag t1 = taintAtSlot(ti, frame, 2); // long high word
            return t0 != null ? t0 : t1;
        }

        // ── unary ops ────────────────────────────────────────────────────────
        if (UNARY_INT.contains(m)) {
            return taintAtSlot(ti, frame, 0);
        }
        if (UNARY_LONG.contains(m)) {
            return taintAtSlot(ti, frame, 1); // long/double high word
        }

        // ── type conversions ─────────────────────────────────────────────────
        if (CONV_FROM1.contains(m)) {
            return taintAtSlot(ti, frame, 0); // 1-slot int/float input
        }
        if (CONV_FROM2.contains(m)) {
            return taintAtSlot(ti, frame, 1); // 2-slot long/double input (high word)
        }

        // ── array load: taint the result when the index is tainted ──────────
        if (ARRAY_LOAD_OPS.contains(m)) {
            return taintAtSlot(ti, frame, 0); // index, always 1-slot int
        }

        return null;
    }

    /**
     * After the instruction has executed, attach the pre-captured TaintTag to the
     * result that now sits on top of the operand stack.
     *
     * Uses addOperandAttr / addLongOperandAttr so that SPF's own symbolic-expression
     * attrs are never overwritten — the taint tag is simply appended to the attr list.
     */
    private void applyArithmeticTaint(ThreadInfo ti, Instruction insn, TaintTag tag) {
        StackFrame frame = ti.getModifiableTopFrame();
        if (frame == null) return;

        String m = insn.getMnemonic();
        if (TWO_SLOT_RESULT.contains(m)) {
            // Long / double result: attr lives at the high-word slot (offset 1 from top).
            frame.addLongOperandAttr(tag);
        } else {
            frame.addOperandAttr(tag);
        }

        String line = "[TaintPropag] " + insn.getMethodInfo().getFullName()
            + " @" + insn.getPosition() + " " + m + " => " + tag;
        System.out.println(line);
        trace(line);
    }

    /**
     * Return the first TaintTag at operand-stack slot {@code offset} from the top.
     * Checks the slot's operand attr; if the slot holds a heap reference also checks
     * the heap object's object attr.
     */
    private TaintTag taintAtSlot(ThreadInfo ti, StackFrame frame, int offset) {
        TaintTag tag = firstTaint(frame.getOperandAttr(offset));
        if (tag != null) return tag;
        if (frame.isOperandRef(offset)) {
            int ref = frame.peek(offset);
            if (ref != MJIEnv.NULL) {
                return firstTaint(ti.getHeap().get(ref));
            }
        }
        return null;
    }

    // ── invoke / native-return handlers ──────────────────────────────────────

    private void handleInvoke(ThreadInfo ti, JVMInvokeInstruction insn) {
        MethodInfo mi;
        try {
            mi = insn.getInvokedMethod(ti);
        } catch (ClassInfoException cie) {
            // Invoked class cannot be resolved (e.g. garbled class name from
            // obfuscated DES-decrypted strings). Skip taint analysis for this call.
            return;
        }
        if (mi == null) return;

        boolean isAppNative = mi.isNative() && !isFrameworkClass(mi.getClassName());
        boolean isSink = matchesAny(mi, sinks) && !suppressedNativeSink(mi, isAppNative);

        // Capture argument refs for any native method with declared effects, so
        // they can be replayed once it returns.  Must run before the early exits
        // below and regardless of taint: a native *source* produces a secret out
        // of entirely untainted inputs.
        captureEffectArgs(ti, insn, mi);

        // App native methods are not necessarily final sinks on the Java side.
        // They are JNI boundaries for Kharon, so record tainted arguments even
        // when the native method name does not match taint.sinks.
        if (!isSink && !(isAppNative && handoffFile != null)) return;

        // Explicit taint: argument operand/heap attrs or array element attrs
        TaintTag tag = firstTaintFromInvoke(ti, insn, mi);
        boolean implicit = false;
        if (tag == null) {
            // Implicit taint: current frame was tagged by an earlier branch on tainted data
            tag = firstTaint(ti.getTopFrame());
            implicit = (tag != null);
        }
        if (tag != null) {
            if (isSink) {
                String kind = implicit ? " (implicit)" : "";
                String line = "[TaintListener] *** TAINT FLOW DETECTED" + kind + ": "
                    + tag + " -> " + mi.getFullName() + " ***";
                System.out.println(line);
                trace(line);
            }

            // For native app methods: record per-argument taint detail so Kharon can
            // initialize the correct symbolic variables as tainted before angr SE.
            if (isAppNative && handoffFile != null && !implicit) {
                recordNativeHandoff(ti, insn, mi);
            }
            return;
        }

        // No taint on the arguments themselves — but a native call whose argument
        // *contains* tainted data (c.data, d.str, foo.data) is still a boundary
        // Kharon must inspect, since the native body can read the field and leak
        // it. This only opens the handoff; the Java-side verdict is unchanged,
        // so it cannot create a false positive on its own.
        if (isAppNative && handoffFile != null) {
            TaintTag reachable = reachableTaintFromInvoke(ti, insn);
            if (reachable != null) {
                trace("[TaintListener] native boundary with field-reachable taint: "
                      + mi.getFullName() + " <- " + reachable);
                recordNativeHandoff(ti, insn, mi);

                // A confirmed native sink that Kharon verified reads a tainted
                // field of its argument (native_complexdata's send reads c.data
                // via a getter) is a real leak, even though the taint sits in a
                // field rather than on the argument itself. Gated on Kharon's
                // confirmation, so it cannot over-report on its own.
                if (isSink && matchesNativeSpec(mi, nativeConfirmedSinks)) {
                    String line = "[TaintListener] *** TAINT FLOW DETECTED (field-reachable): "
                        + reachable + " -> " + mi.getFullName() + " ***";
                    System.out.println(line);
                    trace(line);
                }
            }
        }
    }

    /**
     * True when a name-matched sink should be ignored because it is an
     * app-declared native method that Kharon analysed and did not confirm.
     *
     * The Java side sees only that a tainted value flows into a method whose
     * name matches taint.sinks; whether the native body leaks it is decided by
     * Kharon's symbolic execution of the .so.  Methods Kharon never analysed
     * are left alone, so this can only remove findings Kharon actively cleared.
     */
    private boolean suppressedNativeSink(MethodInfo mi, boolean isAppNative) {
        if (!requireConfirmedNativeSinks || !isAppNative) return false;
        if (!matchesNativeSpec(mi, nativeAnalyzed)) return false;
        boolean confirmed = matchesNativeSpec(mi, nativeConfirmedSinks);
        if (!confirmed) {
            String line = "[TaintListener] native sink not confirmed by Kharon, "
                + "suppressing name match: " + mi.getFullName();
            System.out.println(line);
            trace(line);
        }
        return !confirmed;
    }

    // ── native effects: replaying what the native body did ───────────────────

    /** Effects declared for this method, or an empty list. */
    private ArrayList<NativeEffect> effectsFor(MethodInfo mi) {
        ArrayList<NativeEffect> out = new ArrayList<>();
        if (nativeEffects == null || nativeEffects.isEmpty()) return out;
        String fullName = mi.getFullName();
        for (NativeEffect e : nativeEffects) {
            if (e.signature.indexOf('(') >= 0 ? fullName.equals(e.signature)
                                              : fullName.contains(e.signature)) {
                out.add(e);
            }
        }
        return out;
    }

    /**
     * Pre-invoke: remember the argument references of a native call that has
     * declared effects, since they are popped by the time it returns.
     */
    private void captureEffectArgs(ThreadInfo ti, JVMInvokeInstruction insn, MethodInfo mi) {
        if (!mi.isNative() || effectsFor(mi).isEmpty()) return;
        Object[] args = insn.getArgumentValues(ti);
        StackFrame frame = ti.getTopFrame();
        if (frame == null) return;

        // Java argument order, receiver excluded — the same indexing Kharon uses
        // when it reports "argN".
        String[] typeNames = mi.getArgumentTypeNames();
        int nArgs = typeNames == null ? 0 : typeNames.length;
        int[] refs = new int[nArgs];
        int argSize = insn.getArgSize();
        // Operand slots run right-to-left: the last argument sits nearest the top.
        // getArgumentTypeNames() gives dotted names ("org.x.ComplexData", "long"),
        // not descriptors, so slot width is derived here rather than via Types.
        int slot = 0;
        for (int i = nArgs - 1; i >= 0 && slot < argSize; i--) {
            refs[i] = frame.isOperandRef(slot) ? frame.peek(slot) : MJIEnv.NULL;
            String t = typeNames[i];
            slot += ("long".equals(t) || "double".equals(t)) ? 2 : 1;
        }
        pendingEffectMethod  = mi;
        pendingEffectArgRefs = refs;
    }

    /**
     * Post-return: apply every declared effect of the native method that just
     * returned.  Materialises missing objects along the way — without that,
     * `Foo f = setField(c)` leaves both `f` and `c.foo` null and the app NPEs
     * before it ever reaches its sink.
     */
    private void applyNativeEffects(ThreadInfo ti, JVMReturnInstruction insn) {
        MethodInfo mi = insn.getMethodInfo();
        if (mi == null || mi != pendingEffectMethod) return;
        int[] argRefs = pendingEffectArgRefs;
        pendingEffectMethod  = null;
        pendingEffectArgRefs = null;

        StackFrame caller = ti.getModifiableTopFrame();
        if (caller == null) return;

        for (NativeEffect e : effectsFor(mi)) {
            try {
                applyNativeEffect(ti, caller, mi, argRefs, e);
            } catch (Throwable t) {
                // An effect is advisory: a malformed path or an unloadable class
                // must not abort the analysis run.
                trace("[TaintEffect] could not apply " + e.target + "." + e.fieldPath
                      + " on " + mi.getFullName() + ": " + t);
            }
        }
    }

    /**
     * Resolve an alias path ("argM" or "argM.f1.f2") to the heap reference of
     * the object it names, walking instance fields from the argument. Returns
     * MJIEnv.NULL if the path is empty, malformed, or hits a null link.
     */
    private int resolveAliasRef(ThreadInfo ti, int[] argRefs, String aliasPath) {
        if (aliasPath == null || aliasPath.isEmpty() || !aliasPath.startsWith("arg")) {
            return MJIEnv.NULL;
        }
        String[] parts = aliasPath.split("\\.");
        int idx;
        try {
            idx = Integer.parseInt(parts[0].substring(3));
        } catch (NumberFormatException nfe) {
            return MJIEnv.NULL;
        }
        if (argRefs == null || idx < 0 || idx >= argRefs.length) return MJIEnv.NULL;
        int ref = argRefs[idx];
        for (int i = 1; i < parts.length && ref != MJIEnv.NULL; i++) {
            ElementInfo ei = ti.getHeap().get(ref);
            if (ei == null) return MJIEnv.NULL;
            FieldInfo fi = ei.getClassInfo().getInstanceField(parts[i]);
            if (fi == null || !fi.isReference()) return MJIEnv.NULL;
            ref = ei.getReferenceField(fi);
        }
        return ref;
    }

    private void applyNativeEffect(ThreadInfo ti, StackFrame caller, MethodInfo mi,
                                   int[] argRefs, NativeEffect e) {
        ElementInfo base;

        // Aliasing: the native returned/stored one of its arguments (or a field
        // of one) verbatim. Resolve the path to that object's actual reference,
        // so its own (possibly deep) taint is what flows — not a fresh, shallower
        // taint.
        int aliasRef = resolveAliasRef(ti, argRefs, e.aliasPath);
        boolean isAlias = aliasRef != MJIEnv.NULL;

        if ("return".equals(e.target)) {
            if (!mi.isReferenceReturnType()) return;
            if (caller.getTopPos() < caller.getLocalVariableCount()) return;
            if (isAlias && e.fieldPath.isEmpty()) {
                // The return IS the aliased object: put it on the stack.
                caller.pop();
                caller.pushRef(aliasRef);
                trace("[TaintEffect] return aliases " + e.aliasPath
                      + " for " + mi.getFullName());
                return;
            }
            int ref = caller.peek();
            if (ref == MJIEnv.NULL) {
                // The native method returned an object SPF never created.
                ElementInfo fresh = newInstance(ti, mi.getReturnTypeName());
                if (fresh == null) return;
                caller.pop();
                caller.pushRef(fresh.getObjectRef());
                trace("[TaintEffect] materialised return " + mi.getReturnTypeName()
                      + " for " + mi.getFullName());
                base = fresh;
            } else {
                base = ti.getHeap().getModifiable(ref);
            }
        } else if (e.target.startsWith("arg")) {
            int idx;
            try {
                idx = Integer.parseInt(e.target.substring(3));
            } catch (NumberFormatException nfe) {
                return;
            }
            if (argRefs == null || idx < 0 || idx >= argRefs.length) return;
            if (argRefs[idx] == MJIEnv.NULL) return;
            base = ti.getHeap().getModifiable(argRefs[idx]);
        } else {
            return;
        }
        if (base == null) return;

        // Walk the field path, creating objects for null links along the way.
        String[] path = e.fieldPath.isEmpty() ? new String[0] : e.fieldPath.split("\\.");
        for (int i = 0; i < path.length - 1; i++) {
            FieldInfo fi = base.getClassInfo().getInstanceField(path[i]);
            if (fi == null) return;
            int ref = base.getReferenceField(fi);
            if (ref == MJIEnv.NULL) {
                ElementInfo link = newInstance(ti, fi.getType());
                if (link == null) return;
                base.setReferenceField(fi, link.getObjectRef());
                base = link;
            } else {
                base = ti.getHeap().getModifiable(ref);
            }
            if (base == null) return;
        }

        TaintTag tag = new TaintTag(e.sourceApi, mi.getFullName() + " (native effect)");

        if (path.length == 0) {
            // The target object itself carries the result.
            if (e.tainted) addTaint(base, tag);
            else base.removeObjectAttr(tag);
            logEffect(mi, e, tag);
            return;
        }

        FieldInfo fi = base.getClassInfo().getInstanceField(path[path.length - 1]);
        if (fi == null) return;

        if (!fi.isReference()) {
            // Primitive field: the taint rides on the owning object.
            if (e.tainted) addTaint(base, tag);
            logEffect(mi, e, tag);
            return;
        }

        // Aliasing: point the field at the resolved argument object, so its own
        // (possibly deep) taint is what a later read sees.
        if (isAlias) {
            base.setReferenceField(fi, aliasRef);
            base.setFieldAttr(fi, tag);
            addTaint(ti.getHeap().getModifiable(aliasRef), tag);
            logEffect(mi, e, tag);
            return;
        }

        // Write a fresh value into the field.  A sanitiser writes a clean string
        // — which is what the native code did — rather than trying to strip tags
        // off whatever the field happened to hold.
        ElementInfo value = ti.getHeap().newString(
            e.tainted ? "TAINTED_native_" + mi.getBaseName() : "CLEAN_native_" + mi.getBaseName(), ti);
        base.setReferenceField(fi, value.getObjectRef());

        // The tag must be set/cleared on the field slot as well as the value:
        // JPF carries a field attr that GETFIELD copies onto the operand, so a
        // sanitiser that only swapped the reference would leave the old tag to
        // reach the sink anyway.
        if (e.tainted) {
            addTaint(value, tag);
            base.setFieldAttr(fi, tag);
        } else {
            TaintTag stale = base.getFieldAttr(fi, TaintTag.class);
            if (stale != null) base.removeFieldAttr(fi, stale);
        }
        logEffect(mi, e, tag);
    }

    private void logEffect(MethodInfo mi, NativeEffect e, TaintTag tag) {
        String line = "[TaintEffect] " + mi.getBaseName() + " -> " + e.target
            + (e.fieldPath.isEmpty() ? "" : "." + e.fieldPath)
            + (e.tainted ? " := tainted " + tag : " := cleaned (native sanitiser)");
        System.out.println(line);
        trace(line);
    }

    /** Allocate an instance of {@code typeName}, or null if it cannot be resolved. */
    private ElementInfo newInstance(ThreadInfo ti, String typeName) {
        if (typeName == null || typeName.isEmpty()) return null;
        if (typeName.equals("java.lang.String")) {
            return ti.getHeap().newString("", ti);
        }
        ClassInfo ci = ClassInfo.getInitializedClassInfo(typeName, ti);
        if (ci == null || ci.isArray() || ci.isInterface()) return null;
        return ti.getHeap().newObject(ci, ti);
    }

    // ── native taint handoff helpers ─────────────────────────────────────────

    /**
     * Map a Java type name to its JNI equivalent.
     * Used to tell Kharon which JNI type a tainted argument has so the angr
     * backend can choose the right stub to mark as returning tainted data
     * (e.g. GetStringUTFChars for jstring, GetByteArrayElements for jbyteArray).
     */
    private static String jniTypeFor(String javaType) {
        switch (javaType) {
            case "java.lang.String": return "jstring";
            case "java.lang.Object": return "jobject";
            case "java.lang.Class":  return "jclass";
            case "java.lang.Throwable": return "jthrowable";
            case "int":     return "jint";
            case "long":    return "jlong";
            case "boolean": return "jboolean";
            case "byte":    return "jbyte";
            case "char":    return "jchar";
            case "short":   return "jshort";
            case "float":   return "jfloat";
            case "double":  return "jdouble";
            case "byte[]":    return "jbyteArray";
            case "int[]":     return "jintArray";
            case "long[]":    return "jlongArray";
            case "float[]":   return "jfloatArray";
            case "double[]":  return "jdoubleArray";
            case "boolean[]": return "jbooleanArray";
            case "char[]":    return "jcharArray";
            case "short[]":   return "jshortArray";
            default:
                if (javaType.endsWith("[]")) return "jobjectArray";
                return "jobject";
        }
    }

    /**
     * Record per-argument taint detail for a native call site.
     *
     * jniParamIndex layout (same for static and non-static):
     *   0 = JNIEnv*  (never tainted, added by JNI ABI)
     *   1 = jobject (this) or jclass  (for static methods, clazz)
     *   2 = first explicit Java parameter
     *   3 = second explicit Java parameter, ...
     *
     * getArgumentValues() returns the explicit declared parameters ONLY — never
     * the receiver, for either static or instance methods. So argValues[i] is
     * always the i-th explicit parameter, at JNI slot i+2.
     */
    private void recordNativeHandoff(ThreadInfo ti, JVMInvokeInstruction insn, MethodInfo mi) {
        String nativeFqn = mi.getFullName();
        HandoffEntry entry = nativeHandoffs.computeIfAbsent(
                nativeFqn, k -> new HandoffEntry(nativeFqn, mi.isStatic()));

        // Record which entrypoint triggered this call
        MethodInfo callerMethod = ti.getTopFrame().getMethodInfo();
        if (callerMethod != null) {
            entry.callerEntrypoints.add(callerMethod.getFullName());
        }

        // Walk each argument, check for taint, and record it
        Object[] argValues = insn.getArgumentValues(ti);
        Object[] argAttrs  = insn.getArgumentAttrs(ti);
        String[] typeNames = mi.getArgumentTypeNames();  // explicit param types only

        if (argValues == null) return;

        for (int i = 0; i < argValues.length; i++) {
            TaintTag tag = null;
            ArrayList<Integer> taintedElements = null;

            // Slot attr
            if (argAttrs != null && i < argAttrs.length) {
                tag = firstTaint(argAttrs[i]);
            }
            // Heap attr (reference types)
            if (tag == null && argValues[i] instanceof ElementInfo) {
                ElementInfo ei = (ElementInfo) argValues[i];
                tag = firstTaint(ei);
                // Array element attr: for an argument like String[], the taint
                // sits on an element rather than on the array object itself.
                // Detection (firstTaintFromInvoke) already looks here, so the
                // handoff must too — otherwise Kharon is handed a boundary with
                // no tainted argument to follow into the native body.  Record
                // which indices carry it: native code that reads a different
                // element than the one holding the secret does not leak it.
                if (tag == null && ei.isArray()) {
                    taintedElements = new ArrayList<>();
                    tag = taintInArray(ti, ei, taintedElements);
                }
                // Taint held in the object's fields rather than on the object
                // itself. Kharon marks the whole fake object's memory, which is
                // the right granularity: the native body reaches the secret via
                // GetObjectField on exactly that memory.
                if (tag == null) {
                    tag = reachableTaint(ti, ei, MAX_TAINT_DEPTH, new HashSet<Integer>());
                    if (tag != null) taintedElements = null;
                }
            }

            if (tag == null) continue;

            // argValues[i] is the i-th explicit parameter (receiver excluded),
            // whose JNI slot is i+2: slot 0 = JNIEnv*, slot 1 = jobject/jclass,
            // then the explicit parameters. This holds for static and instance
            // methods alike — the earlier receiver/off-by-one adjustment was
            // wrong and mislabelled e.g. setField(c, f)'s tainted f as c.
            String javaType = (typeNames != null && i < typeNames.length)
                              ? typeNames[i] : "java.lang.Object";
            int jniParamIndex = i + 2;

            // Avoid duplicates: same native + same arg + same source across paths
            boolean exists = false;
            for (HandoffArg a : entry.taintedArgs) {
                if (a.javaArgIndex == i && a.taintSource.equals(tag.getSource())) {
                    exists = true;
                    break;
                }
            }
            if (!exists) {
                entry.taintedArgs.add(new HandoffArg(
                    i, jniParamIndex,
                    javaType, jniTypeFor(javaType),
                    tag.getSource(), tag.getOrigin(),
                    taintedElements
                ));
            }
        }
    }

    /** Escape a string for embedding in a JSON literal. */
    private static String jsonEsc(String s) {
        if (s == null) return "";
        return s.replace("\\", "\\\\").replace("\"", "\\\"");
    }

    /** Serialise nativeHandoffs to the handoff JSON file. */
    private void writeHandoffJson() {
        if (handoffFile == null || nativeHandoffs.isEmpty()) return;

        StringBuilder sb = new StringBuilder();
        sb.append("{\n  \"version\": \"1.0\",\n  \"native_calls\": [\n");

        boolean firstEntry = true;
        for (HandoffEntry entry : nativeHandoffs.values()) {
            if (!firstEntry) sb.append(",\n");
            firstEntry = false;

            sb.append("    {\n");
            sb.append("      \"native_fqn\": \"").append(jsonEsc(entry.nativeFqn)).append("\",\n");
            sb.append("      \"is_static\": ").append(entry.isStatic).append(",\n");

            // caller entrypoints array
            sb.append("      \"caller_entrypoints\": [");
            boolean firstEp = true;
            for (String ep : entry.callerEntrypoints) {
                if (!firstEp) sb.append(", ");
                firstEp = false;
                sb.append("\"").append(jsonEsc(ep)).append("\"");
            }
            sb.append("],\n");

            // tainted_args array
            sb.append("      \"tainted_args\": [\n");
            boolean firstArg = true;
            for (HandoffArg arg : entry.taintedArgs) {
                if (!firstArg) sb.append(",\n");
                firstArg = false;
                sb.append("        {\n");
                sb.append("          \"java_arg_index\": ").append(arg.javaArgIndex).append(",\n");
                sb.append("          \"jni_param_index\": ").append(arg.jniParamIndex).append(",\n");
                sb.append("          \"java_type\": \"").append(jsonEsc(arg.javaType)).append("\",\n");
                sb.append("          \"jni_type\": \"").append(jsonEsc(arg.jniType)).append("\",\n");
                sb.append("          \"taint_source\": \"").append(jsonEsc(arg.taintSource)).append("\",\n");
                sb.append("          \"taint_origin\": \"").append(jsonEsc(arg.taintOrigin)).append("\"");
                if (arg.taintedElements != null && !arg.taintedElements.isEmpty()) {
                    sb.append(",\n          \"tainted_element_indices\": [");
                    for (int e = 0; e < arg.taintedElements.size(); e++) {
                        if (e > 0) sb.append(", ");
                        sb.append(arg.taintedElements.get(e));
                    }
                    sb.append("]");
                }
                sb.append("\n        }");
            }
            sb.append("\n      ]\n");
            sb.append("    }");
        }
        sb.append("\n  ]\n}\n");

        File out = new File(handoffFile);
        try {
            File parent = out.getParentFile();
            if (parent != null) parent.mkdirs();
            try (FileWriter fw = new FileWriter(out)) {
                fw.write(sb.toString());
            }
            System.out.println("[TaintHandoff] native boundary file written: " + out.getPath());
        } catch (IOException e) {
            System.out.println("[TaintHandoff] failed to write " + out.getPath() + ": " + e);
        }
    }

    private TaintTag firstTaintFromInvoke(ThreadInfo ti, JVMInvokeInstruction insn, MethodInfo mi) {
        // Path 1: operand-slot attrs on argument positions
        if (insn.hasArgumentAttr(ti, TaintTag.class)) {
            Object[] attrs = insn.getArgumentAttrs(ti);
            if (attrs != null) {
                for (Object attr : attrs) {
                    TaintTag tag = firstTaint(attr);
                    if (tag != null) return tag;
                }
            }
        }

        // Path 2: heap-object attrs and array-element attrs on reference args
        Object[] args = insn.getArgumentValues(ti);
        if (args != null) {
            for (Object arg : args) {
                if (arg instanceof ElementInfo) {
                    ElementInfo ei = (ElementInfo) arg;
                    TaintTag tag = firstTaint(ei);
                    if (tag != null) return tag;
                    // Scan array elements for taint (array callbacks)
                    if (ei.isArray()) {
                        tag = firstTaintInArray(ti, ei);
                        if (tag != null) return tag;
                    }
                }
            }
        }

        // Path 3: receiver ("this") object taint for instance calls.
        // getArgumentValues() only returns explicit declared parameters, never
        // the receiver, so a receiver tainted by an earlier call (e.g.
        // ProcessBuilder.command() tainting `this` via its return-this pattern)
        // would otherwise be invisible to a later no-arg call like start().
        if (!mi.isStatic()) {
            StackFrame frame = ti.getTopFrame();
            int recvSlot = insn.getArgSize() - 1;
            if (frame != null && recvSlot >= 0 && frame.isOperandRef(recvSlot)) {
                int ref = frame.peek(recvSlot);
                if (ref != MJIEnv.NULL) {
                    TaintTag tag = firstTaint(ti.getHeap().get(ref));
                    if (tag != null) return tag;
                }
            }
        }

        return null;
    }

    /**
     * Scan array element attrs (and heap-object attrs of reference elements) for
     * any TaintTag.  Caps the scan at 64 elements to avoid excessive work on
     * large arrays that are unlikely to carry taint past that point.
     */
    private TaintTag firstTaintInArray(ThreadInfo ti, ElementInfo ei) {
        return taintInArray(ti, ei, null);
    }

    // Depth/breadth caps for reachableTaint. Depth 4 covers the wrapper nesting
    // these samples use (ComplexData -> Foo -> String) with room to spare;
    // the field cap bounds work on wide framework objects.
    private static final int MAX_TAINT_DEPTH  = 4;
    private static final int MAX_TAINT_FIELDS = 32;

    /**
     * Find taint reachable from an object through its reference fields.
     *
     * {@link #firstTaint(ElementInfo)} only reads an object's own attr, so taint
     * stored *inside* an argument is invisible: after {@code c.setData(imei)}
     * the tainted String lives in {@code c.data} while {@code c} itself carries
     * no tag. A native call {@code send(c)} then looks clean and no JNI boundary
     * is recorded, so Kharon is never asked whether the native body leaks it.
     *
     * Used only to decide that a native boundary is worth handing to Kharon —
     * deliberately NOT used for Java-side sink reporting, where reachability
     * (as opposed to the value actually flowing to the sink) would over-report.
     */
    private TaintTag reachableTaint(ThreadInfo ti, ElementInfo ei,
                                    int depth, HashSet<Integer> seen) {
        if (ei == null || depth < 0) return null;
        if (!seen.add(ei.getObjectRef())) return null;   // cycle guard

        TaintTag tag = firstTaint(ei);
        if (tag != null) return tag;

        if (ei.isArray()) {
            tag = taintInArray(ti, ei, null);
            if (tag != null) return tag;
            String cn = ei.getClassInfo() == null ? "" : ei.getClassInfo().getName();
            if (cn.startsWith("[L") || cn.startsWith("[[")) {
                int len = Math.min(ei.arrayLength(), MAX_TAINT_FIELDS);
                for (int i = 0; i < len; i++) {
                    int ref = ei.getReferenceElement(i);
                    if (ref == MJIEnv.NULL) continue;
                    tag = reachableTaint(ti, ti.getHeap().get(ref), depth - 1, seen);
                    if (tag != null) return tag;
                }
            }
            return null;
        }

        int n = Math.min(ei.getNumberOfFields(), MAX_TAINT_FIELDS);
        for (int i = 0; i < n; i++) {
            FieldInfo fi = ei.getFieldInfo(i);
            if (fi == null || !fi.isReference()) continue;
            int ref = ei.getReferenceField(fi);
            if (ref == MJIEnv.NULL) continue;
            tag = reachableTaint(ti, ti.getHeap().get(ref), depth - 1, seen);
            if (tag != null) return tag;
        }
        return null;
    }

    /** Reachable taint on any argument of a native call, or null. */
    private TaintTag reachableTaintFromInvoke(ThreadInfo ti, JVMInvokeInstruction insn) {
        Object[] args = insn.getArgumentValues(ti);
        if (args == null) return null;
        for (Object arg : args) {
            if (!(arg instanceof ElementInfo)) continue;
            TaintTag tag = reachableTaint(
                ti, (ElementInfo) arg, MAX_TAINT_DEPTH, new HashSet<Integer>());
            if (tag != null) return tag;
        }
        return null;
    }

    /**
     * Scan array elements for taint, optionally collecting the indices that
     * carry it.
     *
     * Which element is tainted matters to the native side: a library that reads
     * arr[4] does not leak an IMEI stored at arr[1].  Kharon can only make that
     * distinction if the handoff says which indices to mark, so callers pass a
     * list here to record them.
     *
     * @param taintedIndices if non-null, every tainted index found is added and
     *                       the scan continues; otherwise it stops at the first.
     */
    private TaintTag taintInArray(ThreadInfo ti, ElementInfo ei,
                                  ArrayList<Integer> taintedIndices) {
        int len = Math.min(ei.arrayLength(), 64);
        String className = ei.getClassInfo().getName();
        // Reference arrays: "[Ljava/lang/String;" starts with "[L", multi-dim with "[["
        boolean isRefArray = className.startsWith("[L") || className.startsWith("[[");
        TaintTag first = null;

        for (int i = 0; i < len; i++) {
            TaintTag tag = firstTaint(ei.getElementAttr(i));
            if (tag == null && isRefArray) {
                int ref = ei.getReferenceElement(i);
                if (ref != MJIEnv.NULL) {
                    tag = firstTaint(ti.getHeap().get(ref));
                }
            }
            if (tag == null) continue;
            if (first == null) first = tag;
            if (taintedIndices == null) return first;
            if (!taintedIndices.contains(i)) taintedIndices.add(i);
        }
        return first;
    }

    // ── taint-through library calls ───────────────────────────────────────────

    /**
     * Pre-exec: if the invoke targets a TAINT_THROUGH library method and at least
     * one argument is tainted, capture the tag so it can be applied to the return
     * value after the call completes.
     *
     * Void methods (e.g. String.getChars) are handled by a separate pending
     * mechanism: see pendingVoidArgRefs / instructionExecuted.
     */
    private TaintTag captureInvokeTaint(ThreadInfo ti, JVMInvokeInstruction insn) {
        MethodInfo mi = insn.getInvokedMethod(ti);
        if (mi == null) return null;

        boolean isTaintThrough = TAINT_THROUGH.contains(mi.getName());
        boolean isNativeTaintThrough = mi.isNative()
            && nativeTaintThrough != null && !nativeTaintThrough.isEmpty()
            && matchesAny(mi, nativeTaintThrough);

        if (!isTaintThrough && !isNativeTaintThrough) return null;
        TaintTag tag = firstTaintFromInvoke(ti, insn, mi);
        if (tag == null) return null;

        if (isNativeTaintThrough) {
            String line = "[TaintNativeThrough] " + mi.getFullName() + " => " + tag;
            System.out.println(line);
            trace(line);
        }

        if (mi.getReturnTypeName().equals("void")) {
            // Void TAINT_THROUGH methods (String.getChars, Formatter.format, …) write
            // tainted data into reference-type arguments.  Collect arg refs now (pre-exec
            // while args are still on the stack) and tag them in instructionExecuted.
            StackFrame frame = ti.getTopFrame();
            if (frame != null) {
                int argSize = insn.getArgSize();
                int[] refs = new int[argSize];
                boolean[] isRef = new boolean[argSize];
                for (int slot = 0; slot < argSize; slot++) {
                    isRef[slot] = frame.isOperandRef(slot);
                    refs[slot] = frame.peek(slot);
                }
                pendingVoidTag = tag;
                pendingVoidArgRefs = refs;
                pendingVoidArgIsRef = isRef;
            }
            return null;
        }
        return tag;
    }

    /**
     * Post-exec: store the pre-captured taint tag on the callee frame so that
     * applyReturnTaint can retrieve it when the callee returns.
     *
     * Works for both native callees (NativeStackFrame on top, peer has run) and
     * Java callees (fresh JVMStackFrame on top with an empty operand stack).
     */
    private void applyInvokeTaint(ThreadInfo ti, Instruction insn, TaintTag tag) {
        if (!(insn instanceof JVMInvokeInstruction)) return;
        MethodInfo mi = ((JVMInvokeInstruction) insn).getInvokedMethod();
        if (mi == null || mi.getReturnTypeName().equals("void")) return;

        StackFrame frame = ti.getModifiableTopFrame();
        if (frame == null) return;

        // Store tag on the callee frame (NativeStackFrame for MJI methods, or fresh
        // JVMStackFrame for Java methods with empty operand stack). applyReturnTaint
        // will retrieve the tag at the corresponding return instruction.
        frame.addFrameAttr(tag);
    }

    /**
     * Post-exec for any return instruction: if applyInvokeTaint stored a taint tag
     * on the callee's frame (native or Java), apply it to the return value now on
     * the caller's operand stack.
     *
     * Handles both NATIVERETURN (taint-through native methods like StringBuilder.append)
     * and regular ARETURN (taint-through Java methods like Arrays.toString).
     */
    private void applyReturnTaint(ThreadInfo ti, JVMReturnInstruction insn) {
        StackFrame returnFrame = insn.getReturnFrame();
        if (returnFrame == null) return;

        TaintTag tag = firstTaint(returnFrame);
        if (tag == null) return;

        MethodInfo mi = insn.getMethodInfo();
        if (mi == null || mi.getReturnTypeName().equals("void")) return;

        StackFrame callerFrame = ti.getModifiableTopFrame();
        if (callerFrame == null) return;
        if (callerFrame.getTopPos() < callerFrame.getLocalVariableCount()) return;

        if (mi.isReferenceReturnType()) {
            int ref = callerFrame.peek();
            if (ref == MJIEnv.NULL && insn instanceof NATIVERETURN) {
                // SkippedNativeMethodInfo returns integer 0 (NULL ref).
                // Replace with a synthetic tainted string so taint propagates
                // through subsequent field/operand accesses.
                ElementInfo ei = ti.getHeap().newString("TAINTED_native_" + mi.getBaseName(), ti);
                addTaint(ei, tag);
                callerFrame.pop();
                callerFrame.pushRef(ei.getObjectRef());
            } else if (ref != MJIEnv.NULL) {
                addTaint(ti.getHeap().get(ref), tag);
            }
            callerFrame.addOperandAttr(tag);
        } else {
            byte retType = mi.getReturnTypeCode();
            if (retType == Types.T_DOUBLE || retType == Types.T_LONG) {
                callerFrame.addLongOperandAttr(tag);
            } else {
                callerFrame.addOperandAttr(tag);
            }
        }

        String line = "[TaintPropag] " + mi.getFullName() + " (through) => " + tag;
        System.out.println(line);
        trace(line);
    }

    // ── implicit flow via branch conditions ───────────────────────────────────

    /**
     * Pre-exec: check whether a branch instruction's comparison operand(s) carry
     * taint.  Returns the tag so it can be recorded in the frame after the branch.
     */
    private TaintTag captureBranchTaint(ThreadInfo ti, Instruction insn) {
        if (!BRANCH_OPS.contains(insn.getMnemonic())) return null;
        StackFrame frame = ti.getTopFrame();
        if (frame == null) return null;
        String m = insn.getMnemonic();
        if (m.startsWith("if_icmp") || m.startsWith("if_acmp")) {
            // Two 1-slot operands
            TaintTag t0 = taintAtSlot(ti, frame, 0);
            TaintTag t1 = taintAtSlot(ti, frame, 1);
            return t0 != null ? t0 : t1;
        }
        // One operand (ifnull, ifeq, …)
        return taintAtSlot(ti, frame, 0);
    }

    /**
     * Post-exec: record implicit taint in the frame attr.  Any sink call reached
     * later in the same frame is then considered an implicit taint flow.
     *
     * Note: this is conservative — once a frame is marked, ALL subsequent sink
     * calls in that frame are flagged even if they are not data-dependent on the
     * tainted branch condition.
     */
    private void propagateImplicitTaint(ThreadInfo ti, TaintTag tag) {
        StackFrame frame = ti.getModifiableTopFrame();
        if (frame == null) return;
        addTaint(frame, tag);
        String line = "[TaintImplicit] branch on tainted value: " + tag
            + " in " + frame.getMethodInfo().getFullName();
        System.out.println(line);
        trace(line);
    }

    /**
     * Fires in instructionExecuted after any return instruction completes —
     * including NATIVERETURN (which extends JVMReturnInstruction).
     *
     * At this point the callee frame has already been popped and the return
     * value sits on top of the caller's operand stack.  Taint is injected here
     * so both native and pure-Java source methods are handled uniformly.
     */
    private void handleSourceReturn(ThreadInfo ti, JVMReturnInstruction insn) {
        MethodInfo mi = insn.getMethodInfo();
        if (mi == null) return;
        String sourceSpec = matchingSpec(mi, sources);
        if (sourceSpec == null) return;

        StackFrame callerFrame = ti.getModifiableTopFrame();
        if (callerFrame == null) return;

        // Guard: native methods that fail to push a return value leave the
        // operand stack empty; addOperandAttr would assert-fail in that case.
        if (callerFrame.getTopPos() < callerFrame.getLocalVariableCount()) return;

        TaintTag tag = new TaintTag(sourceSpec, mi.getFullName());

        // For reference return types: if the callee returned null/0, replace it
        // with a synthetic heap string so the tag can propagate through later
        // ALOAD / GETFIELD / invoke instructions.
        if (mi.isReferenceReturnType()) {
            int ref = callerFrame.peek();
            if (ref == MJIEnv.NULL) {
                ElementInfo ei = ti.getHeap().newString("TAINTED_" + mi.getBaseName(), ti);
                addTaint(ei, tag);
                callerFrame.pop();
                callerFrame.pushRef(ei.getObjectRef());
                String allocLine = "[TaintListener] SOURCE allocated: " + mi.getBaseName();
                System.out.println(allocLine);
                trace(allocLine);
            } else {
                addTaint(ti.getHeap().get(ref), tag);
            }
        }

        // For double/long (2-slot) returns, taint lives at the high-word slot
        // (offset 1); use addLongOperandAttr so captureArithmeticTaint finds it.
        byte retType = mi.getReturnTypeCode();
        if (retType == Types.T_DOUBLE || retType == Types.T_LONG) {
            callerFrame.addLongOperandAttr(tag);
        } else {
            callerFrame.addOperandAttr(tag);
        }

        String line = "[TaintListener] SOURCE found: " + tag;
        System.out.println(line);
        trace(line);
    }
}
