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
import gov.nasa.jpf.vm.ElementInfo;
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
        "i2l","i2d","f2l","f2d","l2d","d2l"
    ));

    // Java library methods that propagate taint from any argument to the return value.
    // Covers string manipulation, encoding, collection read-back, and byte conversion.
    private static final Set<String> TAINT_THROUGH = new HashSet<>(Arrays.asList(
        "append", "toString", "concat", "valueOf", "format",
        "substring", "trim", "toLowerCase", "toUpperCase",
        "replace", "replaceAll", "replaceFirst", "intern",
        "strip", "stripLeading", "stripTrailing",
        "getBytes", "toCharArray", "encode", "decode",
        "wrap", "copyOf", "copyOfRange", "join", "split",
        "get", "put", "add", "set",
        // java.util.regex: taint on the input CharSequence propagates to the Matcher
        // and from the Matcher to any group() / replaceAll() result.
        "matcher", "group", "replaceFirst", "appendReplacement", "appendTail"
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

    private static final class HandoffArg {
        final int    javaArgIndex;   // index in getArgumentValues() — 0 = receiver for virtual
        final int    jniParamIndex;  // index in JNI C signature — 0=env, 1=this/jclass, 2+=params
        final String javaType;       // e.g. "java.lang.String", "byte[]"
        final String jniType;        // e.g. "jstring", "jbyteArray", "jint"
        final String taintSource;    // TaintTag.source  (matches source spec, e.g. "getDeviceId")
        final String taintOrigin;    // TaintTag.origin  (full method FQN)

        HandoffArg(int javaArgIndex, int jniParamIndex,
                   String javaType, String jniType,
                   String taintSource, String taintOrigin) {
            this.javaArgIndex  = javaArgIndex;
            this.jniParamIndex = jniParamIndex;
            this.javaType      = javaType;
            this.jniType       = jniType;
            this.taintSource   = taintSource;
            this.taintOrigin   = taintOrigin;
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
        if (ei != null && tag != null && ei.getObjectAttr(TaintTag.class) == null) {
            ei.addObjectAttr(tag);
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
            "sendTextMessage", "sendDataMessage", "openConnection");
        handoffFile = conf.getString("taint.handoff.file", null);
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
        "android.telephony.TelephonyManager",
        "android.location.Location",
        "libcore.io.OsConstants",
        "libcore.io.Posix",
        "dalvik.system.VMRuntime",
        "dalvik.system.VMStack",
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
        MethodInfo mi = insn.getInvokedMethod(ti);
        if (mi == null) return;

        boolean isSink = matchesAny(mi, sinks);
        boolean isAppNative = mi.isNative() && !isFrameworkClass(mi.getClassName());

        // App native methods are not necessarily final sinks on the Java side.
        // They are JNI boundaries for Kharon, so record tainted arguments even
        // when the native method name does not match taint.sinks.
        if (!isSink && !(isAppNative && handoffFile != null)) return;

        // Explicit taint: argument operand/heap attrs or array element attrs
        TaintTag tag = firstTaintFromInvoke(ti, insn);
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
        }
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
     * javaArgIndex in getArgumentValues():
     *   0 = receiver (this) for virtual calls, or first param for static
     *   1 = first explicit param for virtual, or second param for static, ...
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

            // Slot attr
            if (argAttrs != null && i < argAttrs.length) {
                tag = firstTaint(argAttrs[i]);
            }
            // Heap attr (reference types)
            if (tag == null && argValues[i] instanceof ElementInfo) {
                tag = firstTaint((ElementInfo) argValues[i]);
            }

            if (tag == null) continue;

            // Determine Java type for this argument slot
            String javaType;
            int jniParamIndex;
            if (!mi.isStatic() && i == 0) {
                // Receiver (this)
                javaType     = mi.getClassName();
                jniParamIndex = 1;   // JNI: obj/this at position 1
            } else {
                int explicitIdx = mi.isStatic() ? i : i - 1;
                javaType = (typeNames != null && explicitIdx >= 0 && explicitIdx < typeNames.length)
                           ? typeNames[explicitIdx] : "java.lang.Object";
                // Explicit Java parameters always start at JNI slot 2:
                // slot 0 = JNIEnv*, slot 1 = jobject/jclass.
                jniParamIndex = explicitIdx + 2;
            }

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
                    tag.getSource(), tag.getOrigin()
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
                sb.append("          \"taint_origin\": \"").append(jsonEsc(arg.taintOrigin)).append("\"\n");
                sb.append("        }");
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

    private TaintTag firstTaintFromInvoke(ThreadInfo ti, JVMInvokeInstruction insn) {
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

        return null;
    }

    /**
     * Scan array element attrs (and heap-object attrs of reference elements) for
     * any TaintTag.  Caps the scan at 64 elements to avoid excessive work on
     * large arrays that are unlikely to carry taint past that point.
     */
    private TaintTag firstTaintInArray(ThreadInfo ti, ElementInfo ei) {
        int len = Math.min(ei.arrayLength(), 64);
        String className = ei.getClassInfo().getName();
        // Reference arrays: "[Ljava/lang/String;" starts with "[L", multi-dim with "[["
        boolean isRefArray = className.startsWith("[L") || className.startsWith("[[");

        for (int i = 0; i < len; i++) {
            TaintTag tag = firstTaint(ei.getElementAttr(i));
            if (tag != null) return tag;
            if (isRefArray) {
                int ref = ei.getReferenceElement(i);
                if (ref != MJIEnv.NULL) {
                    tag = firstTaint(ti.getHeap().get(ref));
                    if (tag != null) return tag;
                }
            }
        }
        return null;
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
        if (!TAINT_THROUGH.contains(mi.getName())) return null;
        TaintTag tag = firstTaintFromInvoke(ti, insn);
        if (tag == null) return null;

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
            if (ref != MJIEnv.NULL) {
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
