package gov.nasa.jpf.symbc;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;
import java.util.logging.Logger;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNodeImpl;

import antlr4.smtlib.SMTLIBv2Lexer;
import antlr4.smtlib.SMTLIBv2Parser;
import antlr4.smtlib.SMTLIBv2Parser.HexadecimalContext;
import antlr4.smtlib.SMTLIBv2Parser.Qual_identiferContext;
import antlr4.smtlib.SMTLIBv2Parser.TermContext;
import choco.cp.solver.constraints.global.tree.structure.internalStructure.graphStructures.algorithms.ArticulationPoints;
import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.JVMNativeStackFrame;
import gov.nasa.jpf.jvm.JVMStackFrame;
import gov.nasa.jpf.jvm.bytecode.EXECUTENATIVE;
import gov.nasa.jpf.jvm.bytecode.JVMInvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.JVMReturnInstruction;
import gov.nasa.jpf.report.ConsolePublisher;
import gov.nasa.jpf.report.Publisher;
import gov.nasa.jpf.report.PublisherExtension;
import gov.nasa.jpf.symbc.SymbolicListener.MethodSummary;
import gov.nasa.jpf.symbc.bytecode.BytecodeUtils;
import gov.nasa.jpf.symbc.bytecode.INVOKESPECIAL;
import gov.nasa.jpf.symbc.bytecode.INVOKESTATIC;
import gov.nasa.jpf.symbc.concolic.PCAnalyzer;
import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.LogicalORLinearIntegerConstraints;
import gov.nasa.jpf.symbc.numeric.Operator;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.SymbolicStringBuilder;
import gov.nasa.jpf.util.LogManager;
import gov.nasa.jpf.util.MethodSpec;
import gov.nasa.jpf.util.Pair;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.Heap;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.NativeMethodInfo;
import gov.nasa.jpf.vm.NativePeer;
import gov.nasa.jpf.vm.NativeStackFrame;
import gov.nasa.jpf.vm.SkippedMethodInfo;
import gov.nasa.jpf.vm.SkippedNativeMethodInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.Types;
import gov.nasa.jpf.vm.VM;
import main.corana.emulator.semantics.Environment;
import main.corana.external.connector.ArithmeticUtils;
import main.corana.external.connector.SetupJNI;
import main.corana.pojos.BitVec;

public class NativeListener extends PropertyListenerAdapter  {
	private Map<String, MethodSummary> allSummaries;
    private String currentMethodName = "";
    private static String[] skip_spec = null;
    private static boolean skipNatives = false;
	private SetupJNI su;
	private static String outputPath = "";
	Logger currentLog;
	private static boolean isSkip = false;
	

    private static boolean initialized = false;
    private String libraryPath;
   
  
    private void init (Config conf){
        if (!initialized){
          skip_spec = conf.getStringArray("nhandler.spec.skip");
          skipNatives = conf.getBoolean("nhandler.skipNative");
          initialized = true;
          libraryPath = conf.getString("librarypath");
          outputPath = conf.getString("output");
      	  File dir = new File(this.libraryPath);
      	  su = new SetupJNI(dir);
        }
      }
    

    @Override
    public void classLoaded (VM vm, ClassInfo ci){
      init(vm.getConfig());
      //skipNatives(ci);
      processSkipped(ci);
    }
    private void skipNatives (ClassInfo ci){
        MethodInfo[] mth = ci.getDeclaredMethodInfos();
        for (MethodInfo mi : mth){
          if (mi.isNative() && !isHandled(mi)){
            skipUnhandledNative(mi);
          }
        }
      }
    private boolean isHandled(MethodInfo mi) {
        NativeMethodInfo nmi = (NativeMethodInfo) mi;
        NativePeer nativePeer = nmi.getNativePeer();

        // check if there is any native peer class associated to the class of this
        // method at all
        if(nativePeer == null) {
          return false;
        }

        Method[] mth = nativePeer.getPeerClass().getMethods();
        for(Method m: mth) {
          String jniName = nmi.getJNIName();
          if(m.getName().equals(jniName) || jniName.contains(m.getName())) {
            return true;
          }
        }

        return false;
      }

    private void processSkipped (ClassInfo ci){
        if (skip_spec != null){
          MethodInfo[] mth = ci.getDeclaredMethodInfos();
          for (MethodInfo mi : mth){
            for (String spec : skip_spec){
              MethodSpec ms = MethodSpec.createMethodSpec(spec);
              if (ms.matches(mi)){
                skipMethod(mi);
              }
            }
          }	
        }
      }
    
    private void skipMethod (MethodInfo mi){
        MethodInfo new_m = new SkippedMethodInfo(mi);
        ClassInfo ci = mi.getClassInfo();
        ci.putDeclaredMethod(new_m);
      }
    
    private void skipUnhandledNative (MethodInfo mi){
        MethodInfo new_m = new SkippedNativeMethodInfo(mi);
        ClassInfo ci = mi.getClassInfo();
        ci.putDeclaredMethod(new_m);
      }
    
	// VM listener interface
    @Override
    public void methodEntered (VM vm, ThreadInfo currentThread, MethodInfo enteredMethod) {
    	System.out.println("======================================================" ); 
    	System.out.println("enter method " + enteredMethod.getBaseName());
    	   	
    }
    
	@Override
	  public void executeInstruction(VM vm, ThreadInfo currentThread, Instruction instructionToExecute) {
		
		Instruction insn = instructionToExecute;
//		if (insn != null && insn.getMethodInfo().getFullName().contains("java.util")) 
//			System.out.println(insn.getMnemonic() + " " + insn.getMethodInfo().getFullName());
		
		if (!vm.getSystemState().isIgnored()) {
           ThreadInfo ti = currentThread;
           Config conf = vm.getConfig();
           if (insn instanceof EXECUTENATIVE) { // CHANGE THISSSSS
               NativeMethodInfo mi = (NativeMethodInfo) ((EXECUTENATIVE) insn).getExecutedMethod();
               ClassInfo ci = mi.getClassInfo();
               
               File dir = new File(this.libraryPath);
           	if (isJNIFunction(mi.getName())) {
	           	 //currentLog.info("Native library " + mi.getJNIName());
	           	 System.out.println(mi.getJNIName());
	             currentThread.skipInstruction(instructionToExecute);
	             
    		} 
           }
		}
		}
	
	@Override
	public void instructionExecuted(VM vm, ThreadInfo currentThread, Instruction nextInstruction, Instruction executedInstruction) {
		
		if (nextInstruction == null || executedInstruction == null) return;
		if (!vm.getSystemState().isIgnored()) {
			Instruction insn = executedInstruction;
            ThreadInfo ti = currentThread;
            Config conf = vm.getConfig();
    		if (insn != null && !insn.getMethodInfo().getFullName().contains("java.util")) {
    			//System.setOut(out);
    			System.out.println("-" + insn.getLineNumber() + " " + insn.toPostExecString());
			}
//         
            if (insn instanceof JVMInvokeInstruction) {
                JVMInvokeInstruction md = (JVMInvokeInstruction) insn;
                String methodName = md.getInvokedMethodName();
                MethodInfo mi = md.getInvokedMethod();
                if (mi == null) {
                	return;
                } 
                ClassInfo ci = mi.getClassInfo();
                String className = ci.getName(); 
              
                int numberOfArgs = md.getArgumentValues(ti).length;
             
                StackFrame sf = ti.getTopFrame();
                String shortName = methodName;
                String longName = mi.getLongName();
                
                
                if (ti.getLastInvokedStackFrame() instanceof JVMNativeStackFrame && isJNIFunction(methodName)) { //INVOKENATIVE              	
                    Map.Entry<Environment, List<String>> returnNative = null;
                    Map.Entry<Environment, List<String>> returnConcreteNative = null;
                    
                    Environment returnConcreteEnv = new Environment();
                    Environment returnEnv = new Environment();
                    List<String> nativePC = new ArrayList();
                
                    JVMNativeStackFrame nativeStack = (JVMNativeStackFrame) ti.getLastInvokedStackFrame() ;
                    MJIEnv envArgs = (MJIEnv) nativeStack.getArguments()[0];
                    
                    if (isNative(currentThread)) {
                      	Heap heap = vm.getSystemState().getHeap();
                        returnNative = runCorana(md, ti); // Execute CORANA and return env in BitVec
                        returnConcreteNative = runConcreteCorana(md, ti);
                    }
                    
                    List<List<Constraint>> nativeConstraints = new ArrayList<>();
                    IntegerExpression returnSym = null;
                    NativeStackFrame nativeFrame = (NativeStackFrame) ti.getTopFrame();
               	 
               	 	StackFrame top = ti.getTopFrame();
               	 	NativeStackFrame ntop = (NativeStackFrame)top;
               	 	Object   ret = null;
               	 	
  //                  if (isJNIFunction(methodName)) {
	               	 	if (returnConcreteNative != null) {
	                    	 returnConcreteEnv = returnConcreteNative.getKey();
	                    	 System.out.println(returnConcreteEnv.toString());
	                                                 
	                    	 MJIEnv   env = ti.getMJIEnv();
	                    	 
	                    	 // System.out.println("SPF pc: " + pc);
	                    	 // get arg types
	                         byte[] argTypes = mi.getArgumentTypes();
	                         String argTypesStr = "";
	                         for (int i = 0; i < argTypes.length; i++) {
	                             argTypesStr = argTypesStr + argTypes[i];
	                             if ((i + 1) < argTypes.length)
	                                 argTypesStr = argTypesStr + ",";
	                         }       
	                    	 ret = new Integer(10);
	                    	 String c = mi.getReturnType();
	                    	 switch (c.charAt(0)) {
		                         case 'B': //"byte";
		                        	 ret = ArithmeticUtils.BitVecToInteger(returnConcreteEnv.register.get('0'));
		                        	 break;
		                         case 'C': //"char";
		                        	 ret = Character.forDigit(ArithmeticUtils.BitVecToInteger(returnConcreteEnv.register.get('0')), 10);
		                        	 break;
		                         case 'D': //"double";
		                        	 ret = ArithmeticUtils.BitVecToDouble(returnConcreteEnv.register.get('0'));
		                        	 break;
		                         case 'F': //"float";
		                        	 ret = ArithmeticUtils.BitVecToDouble(returnConcreteEnv.register.get('0'));
		                        	 break;
		                         case 'I': //"int";
		                        	 ret = ArithmeticUtils.BitVecToInteger(returnConcreteEnv.register.get('0'));
		                        	 break;
		                         case 'L': 
		                        	 ret = ArithmeticUtils.BitVecToInteger(returnConcreteEnv.register.get('0'));
		                        	 break;
		                         case 'V': //"void";
		                        	 break;
		                         case 'Z': //"boolean";
		                        	 ret = ArithmeticUtils.BitVecToInteger(returnConcreteEnv.register.get('0'));
		                        	 break;
	                         }
	                    	 ntop.setReturnValue(ret);
	                    	 System.out.println("Return value:" + ret);
	                
	                    }
	                    if (returnNative != null) {
	                    	 returnEnv = returnNative.getKey();
		                   	 for (String pc : nativePC) {
		                    	 nativeConstraints.add(Utils.preToInorder(pc));
		                     }
		                    // convert from BitVector theory to LIA
		                     returnSym = Utils.toIntegerExpression(returnEnv.register.get('0'));
		                	
		                	 for (List<Constraint> npc : nativeConstraints)  {
		                		 System.out.println("Native Path Condition: " + nativeConstraints.get(0).toString());
		                	 }
		                	 ntop.setReturnAttr(returnSym);
	                    }
	                   
	                    Instruction nextPC = ntop.getPC().getNext();
	                    top.setPC(nextPC);
	
	                    currentThread.setNextPC(nextPC);
 //                   }
                   
                    ChoiceGenerator<?> cg = vm.getChoiceGenerator();
                    if (!(cg instanceof PCChoiceGenerator)) {
                        ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGenerator();
                        while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
                            prev_cg = prev_cg.getPreviousChoiceGenerator();
                        }
                        cg = prev_cg;
                    }	
                    
                    if ((cg instanceof PCChoiceGenerator) && ((PCChoiceGenerator) cg).getCurrentPC() != null) {
                        PathCondition pc = ((PCChoiceGenerator) cg).getCurrentPC();
                        // pc.solve(); //we only solve the pc
                        
                        System.out.println(methodName + " " + numberOfArgs);
                 
                        for (Constraint c : nativeConstraints.get(0)) {
                            pc.appendAllConjuncts(c);
                        }
                        pc.simplify();
                        System.out.println(pc.toString().replace("(null)", ""));
                        if (SymbolicInstructionFactory.concolicMode) { // TODO: cleaner
                            SymbolicConstraintsGeneral solver = new SymbolicConstraintsGeneral();
                            PCAnalyzer pa = new PCAnalyzer();
                            pa.solve(pc, solver);
                        } else
                            pc.solve();
                    	}
                    
                    
                    if (!PathCondition.flagSolved) {
                        return;
                    }
                } 
            } 
            else if (insn instanceof JVMReturnInstruction) {
                MethodInfo mi = insn.getMethodInfo();
                ClassInfo ci = mi.getClassInfo();
                if (null != ci) {	
                    String className = ci.getName();
                    String methodName = mi.getName();
                    String longName = mi.getLongName();
                    int numberOfArgs = mi.getNumberOfArguments();
                   
                    if (((BytecodeUtils.isClassSymbolic(conf, className, mi, methodName))
                            || BytecodeUtils.isMethodSymbolic(conf, mi.getFullName(), numberOfArgs, null))) {
	
                        ChoiceGenerator<?> cg = vm.getChoiceGenerator();
                        if (!(cg instanceof PCChoiceGenerator)) {
                            ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGenerator();
                            while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
                                prev_cg = prev_cg.getPreviousChoiceGenerator();
                            }
                            cg = prev_cg;
                        }
                        if ((cg instanceof PCChoiceGenerator) && ((PCChoiceGenerator) cg).getCurrentPC() != null) {
                            PathCondition pc = ((PCChoiceGenerator) cg).getCurrentPC();
                            // pc.solve(); //we only solve the pc
                            if (SymbolicInstructionFactory.concolicMode) { // TODO: cleaner
                                SymbolicConstraintsGeneral solver = new SymbolicConstraintsGeneral();
                                PCAnalyzer pa = new PCAnalyzer();
                                pa.solve(pc, solver);
                            } else
                                pc.solve();
                            
                            if (!PathCondition.flagSolved) {
                                return;
                            } 
                    }
                }
            } 
   
            }
		}
	}
	
	private boolean isNative(ThreadInfo currentThread) {
		if (currentThread.getLastInvokedStackFrame() != null) {
			return currentThread.getLastInvokedStackFrame().isNative();
		}
		return false;
		
	}
	private boolean isJNIFunction(String methodName) {
		String shortName = methodName.contains("(") ? methodName.substring(0, methodName.indexOf("(")) : methodName;
		return su.getNativeFunction().contains(shortName);
	}
	
	public Map.Entry<Environment, List<String>> runCorana(JVMInvokeInstruction jniMethod, ThreadInfo currentThread) {

		String methodName = jniMethod.getInvokedMethod().getName();
		if (!su.getNativeFunction().contains(methodName)) {
			return null;
		}
		
		su.setLog(true);
	
		long startTime = System.nanoTime();
        Environment initEnv = new Environment();
        ThreadInfo ti = currentThread.getCurrentThread();
        MethodInfo mi = jniMethod.getInvokedMethod();
        
        int numberOfArgs = mi.getArgumentsSize();
        JVMNativeStackFrame nativeStack = (JVMNativeStackFrame) ti.getLastInvokedStackFrame();
        MJIEnv envArgs = (MJIEnv) nativeStack.getArguments()[0];
        
        // sym attrs
        Object[] symArgs = nativeStack.getCallerFrame().getSlotAttrs();
        int localStackBase = nativeStack.getCallerFrame().getLocalVariableCount();
        
        if (symArgs == null && numberOfArgs != 0) return null; // No symbolic args in SPF
        
        if (symArgs != null ) { //void
            //initEnv.register.set('0', ArithmeticUtils.IntegerToBitVec(10));
            for (int i = 1; i < numberOfArgs+1; i++) {
            	Object stackEle = nativeStack.getArguments()[i];
            	Object symElement = symArgs[localStackBase++];
            	if (i < 4) {
                	if (symElement != null) {
                		// Change from LNA to BitVec
                		if (symElement instanceof SymbolicStringBuilder && ((SymbolicStringBuilder) symElement).getstr() == null) {
                			System.out.println("JPF Argument is Symbolic String");
                		} else initEnv.register.set(Character.forDigit(i,  10), new BitVec(symElement.toString()));
                	}
            	} else {
                	if (symElement != null) {
                		// Change from LNA to BitVec
                		BitVec val = new BitVec(symElement.toString());
                	    initEnv.stacks.push(val);
                	}
            	}
            }
        }
 
        Map.Entry<Environment, List<String>> afterEnv = null;
        try {
        	afterEnv = su.execJNI(jniMethod.getInvokedMethod().getName(), initEnv);
        } catch (Exception e) {
        	e.printStackTrace();
        }
        return afterEnv;
        
	}
	
	public Map.Entry<Environment, List<String>> runConcreteCorana(JVMInvokeInstruction jniMethod, ThreadInfo currentThread) {
		
		String methodName = jniMethod.getInvokedMethod().getName();
		String shortName = methodName.contains("(") ? methodName.substring(0, methodName.indexOf("(")) : methodName;
		if (!su.getNativeFunction().contains(methodName)) {
			return null;
		}
		su.setLog(true);
		long startTime = System.nanoTime();
     
        Environment initEnv = new Environment();
        ThreadInfo ti = currentThread.getCurrentThread();
        
        
        MethodInfo mi = jniMethod.getInvokedMethod();
       
        JVMNativeStackFrame nativeStack = (JVMNativeStackFrame) ti.getLastInvokedStackFrame();
        MJIEnv envArgs = (MJIEnv) nativeStack.getArguments()[0];
        
        // sym attrs
        int numberOfArgs = nativeStack.getArguments().length-1;
        Object[] arguments = nativeStack.getArguments();
        byte[] argsTypes = mi.getArgumentTypes(); // without MJIEnv and this
        int type_counter;
        if (arguments != null) { //void
            initEnv.register.set('0', ArithmeticUtils.IntegerToBitVec((Integer) envArgs.hashCode()));
            type_counter = (numberOfArgs > argsTypes.length) ? -1 : 0; // 2nd args is 'this' ref
           
            for (int i = 1; i < arguments.length; i++) {
            	System.out.println("JPF Argument: " + arguments[i].toString());
            	BitVec val = fromJPFArgument(arguments[i], (type_counter < 0) ? -1 : argsTypes[type_counter++]);
            	if (i < 4) {
            		initEnv.register.set(Character.forDigit(i,  10), val);
            	} else {
        	        initEnv.stacks.push(val);
            	}
            }
        }
        System.out.print(initEnv.toString());
        Map.Entry<Environment, List<String>> afterEnv = null;
        try {
        	afterEnv = su.execJNI(mi.getName(), initEnv);
        } catch (Exception e) {
        	e.printStackTrace();
        }
        return afterEnv;
	}
	
	private BitVec fromJPFArgument(Object arg, int... type) {
		BitVec res = null;
		int t_type = (type.length > 0) ? type[0]: -1;
		if (arg instanceof Integer || t_type == Types.T_INT) {
			res = ArithmeticUtils.IntegerToBitVec((Integer) arg);
		} else if (arg instanceof Double || t_type == Types.T_DOUBLE) {
			res = ArithmeticUtils.DoubleToBitVec((Double) arg);
		} 
		// add more
		return res;
	}
	
	protected static class Utils {
		
		public static IntegerExpression toIntegerExpression(BitVec smtBitVec) {
			SMTLIBv2Lexer lexer = new SMTLIBv2Lexer(CharStreams.fromString(smtBitVec.getSym()));
		    CommonTokenStream tokens = new CommonTokenStream(lexer);
		    SMTLIBv2Parser parser = new SMTLIBv2Parser(tokens);
		    ParseTree tree = parser.start().general_response().specific_success_response().get_assertions_response();
		    IntegerExpression constraint = null;
		    if (tree != null) {
		    //printTree(tree);	
		    List<SMTLIBv2Parser.TermContext> childTerms = new ArrayList<>();
		    for (int i = 0; i < tree.getChildCount(); i++) {
		    	if (tree.getChild(i) instanceof SMTLIBv2Parser.TermContext) 
		    		childTerms.add((TermContext) tree.getChild(i));
		    }
		    List<Constraint> constraintList = new ArrayList<>();
		    
		    if (childTerms.size() == 3) { // operation 
		    	//System.err.print(toOperator(childTerms.get(0)));
		    	Object op = toOperator(childTerms.get(0));
		    	if (op instanceof Operator) {
		    		Object childLeft = toExpression(childTerms.get(1));
		    		Object childRight = toExpression(childTerms.get(2));
		    		constraint = new BinaryLinearIntegerExpression((IntegerExpression) childLeft, (Operator) op, (IntegerExpression) childRight);
		    	} 
		    	}
			return constraint; 
		    } else {
		    	// only bitVec 
		    	if (smtBitVec.getSym().contains("SYM")) {
		    	constraint = new SymbolicInteger(smtBitVec.getSym());	
		    	} else 
		    	constraint = new IntegerConstant(ArithmeticUtils.BitVecToInteger(smtBitVec));
		    return constraint;
		    }
		}
		
		public static List<Constraint> preToInorder(String smtLibString) {
			String inStr = "";
			// remove () 
		    SMTLIBv2Lexer lexer = new SMTLIBv2Lexer(CharStreams.fromString(smtLibString));
		    CommonTokenStream tokens = new CommonTokenStream(lexer);
		    SMTLIBv2Parser parser = new SMTLIBv2Parser(tokens);
		    ParseTree tree = parser.start().general_response().specific_success_response().get_assertions_response();
		    //printTree(tree);
		    List<SMTLIBv2Parser.TermContext> childTerms = new ArrayList<>();
		    for (int i = 0; i < tree.getChildCount(); i++) {
		    	if (tree.getChild(i) instanceof SMTLIBv2Parser.TermContext) 
		    		childTerms.add((TermContext) tree.getChild(i));
		    }
		    List<Constraint> constraintList = new ArrayList<>();
		    Object constraint ;
		    if (childTerms.size() == 3) {	 // operation 
		    	//System.err.print(toOperator(childTerms.get(0)));
		    	Object op = toOperator(childTerms.get(0));
		    	if (op instanceof Comparator) {
		    		Object childLeft = toExpression(childTerms.get(1));
		    		Object childRight = toExpression(childTerms.get(2));
		    		if ((childLeft instanceof IntegerExpression) && (childRight instanceof IntegerExpression)) {
		    			constraint = new LinearIntegerConstraint((IntegerExpression) childLeft, (Comparator) op, (IntegerExpression) childRight);
		    			constraintList.add((Constraint) constraint); 
		    		}
		    			else {
		    				if (childLeft instanceof ArrayList) {
				    			constraintList.addAll((Collection<? extends Constraint>) childLeft);
				    			} else constraintList.add((Constraint) childLeft);
		    				if (childRight instanceof ArrayList) {
		    					constraintList.addAll((Collection<? extends Constraint>) childRight);
		    				} else 	constraintList.add((Constraint) childRight);
			    	}
		    	} else if (op instanceof Operator) {
		    		Object childLeft = toExpression(childTerms.get(1));
		    		Object childRight = toExpression(childTerms.get(2));
		    		if (childLeft instanceof ArrayList) {
		    			constraintList.addAll((Collection<? extends Constraint>) childLeft);
		    			} else constraintList.add((Constraint) childLeft);
    				if (childRight instanceof ArrayList) {
    					constraintList.addAll((Collection<? extends Constraint>) childRight);
    				} else 	constraintList.add((Constraint) childRight);
		    		
		    	}
		    	} else if (childTerms.size() == 2 && childTerms.get(0).getText().equals("not")) {
			    	constraint = toNotExpression( childTerms.get(1));
			    	constraintList.add((Constraint) constraint);
			    }
//		    for (Constraint c: constraintList) {
//		    	System.out.println(c.toString());
//		    }
		    
			return constraintList;
		}
		private static void printTree(ParseTree tree) {
			System.err.println(tree.getClass().getSimpleName() + " " + tree.getText() );
			List<SMTLIBv2Parser.TermContext> childTerms = new ArrayList<>();
		    for (int i = 0; i < tree.getChildCount(); i++) {
		    	if (tree.getChild(i) instanceof SMTLIBv2Parser.TermContext) 
		    		childTerms.add((TermContext) tree.getChild(i));
		    		System.err.println(tree.getChild(i).getText() + " " + tree.getChild(i).getClass().getSimpleName());
		    }
		    for (ParseTree child : childTerms) {
		    	printTree(child);
		    }
		    
		}
		private static Object toOperator(ParserRuleContext parserRuleContext) {
			ParseTree simpleSym;
			if (parserRuleContext instanceof TermContext)
				simpleSym = ((TermContext) parserRuleContext).getChild(0).getChild(0).getChild(0);
			else 
				simpleSym = parserRuleContext.getChild(0).getChild(0);
			//assert(simpleSym instanceof SMTLIBv2Parser.SymbolContext);
			SMTLIBv2Parser.SimpleSymbolContext simpleSymCtx = ((SMTLIBv2Parser.SymbolContext) simpleSym).simpleSymbol();
			switch (simpleSymCtx.getText()) {
			// Operator
			case "bvsub":
				return Operator.MINUS;
			case "bvadd":
				return Operator.PLUS;
			case "bvmul":
				return Operator.MUL;
			case "or":
				return Operator.OR;
			// Comparator
			case "and":
				return Operator.AND;
			case "=":
				return Comparator.EQ;
			case "bvuge":
				return Comparator.GE;
			case "bvugt":
				return Comparator.GT;
			case "bvsle":
				return Comparator.LE;
			case "bvslt":
				return Comparator.LT;
			case "bvsgt":
				return Comparator.GT;
			case "not":
				return Comparator.NE;
			default:
				System.err.println("Undefined: " + simpleSymCtx.getText());
				return Comparator.EQ;
			}
		}
		private static Object toNegOperator(ParserRuleContext parserRuleContext) {
			String simpleSym;
			simpleSym = parserRuleContext.getText();
			//assert(simpleSym instanceof SMTLIBv2Parser.SymbolContext);
			switch (simpleSym) {
			// Operator
			case "=":
				return Comparator.NE;
			case "bvuge":
				return Comparator.LT;
			case "bvugt":
				return Comparator.LE;
			case "bvsle":
				return Comparator.GT;
			case "bvslt":
				return Comparator.GE;
			case "not":
				return Comparator.EQ;
			default:
				//System.err.println("Undefined: " + simpleSym);
				return Comparator.EQ;
		}
		}
		private static Comparator getNeg(Comparator op) {
			switch (op) {
				case NE:
					return Comparator.EQ;
				case GE:
					return Comparator.LT;
				case GT:
					return Comparator.LE;
				case LE:
					return Comparator.GT;
				case LT:
					return Comparator.GE;
				case EQ:
					return Comparator.NE;
				default:
					System.err.println("Undefined: " + op);
					return Comparator.EQ;
			}
		}
			
		private static Object toNotExpression (ParserRuleContext smtTree) {
			Object constraint = null;
			if (smtTree instanceof TermContext) {
				List<ParserRuleContext> childTerms = new ArrayList<>();
			    for (int i = 0; i < smtTree.getChildCount(); i++) {
			    	if (!(smtTree.getChild(i) instanceof TerminalNodeImpl)) 
			    		childTerms.add((ParserRuleContext) smtTree.getChild(i));
			    }
			    if (childTerms.size() == 3) { // operation 
			    	//System.err.print(toOperator(childTerms.get(0)));
			    	Object op = toNegOperator(childTerms.get(0));
			    	Object childLeft = toExpression(childTerms.get(1));
		    		Object childRight = toExpression(childTerms.get(2));
		    		if (op instanceof Comparator) {
			    		if (childLeft instanceof IntegerExpression && childRight instanceof IntegerExpression) {
			    		constraint = new LinearIntegerConstraint((IntegerExpression) childLeft, getNeg((Comparator) op), (IntegerExpression) childRight);
			    		} else if (childLeft instanceof LogicalORLinearIntegerConstraints || childRight instanceof LogicalORLinearIntegerConstraints ) {
			    			// We only choose one
			    			constraint = (childLeft instanceof LogicalORLinearIntegerConstraints) ? childRight: childLeft;
			    		}
			    	} else {
			    		if (op == Operator.OR) {
			    			//LogicalORLinearIntegerConstraints 
			    			List<LinearIntegerConstraint> cList = new ArrayList<>();
			    			cList.add( (LinearIntegerConstraint)childLeft);
			    			cList.add( (LinearIntegerConstraint)childRight);
			    			constraint = new LogicalORLinearIntegerConstraints(cList);
			    			//constraint = new BinaryNonLinearIntegerExpression((IntegerExpression) childLeft, (Operator) op, (IntegerExpression) childRight);
			    		} else if (op == Operator.AND) {
			    			List<LinearIntegerConstraint> cList = new ArrayList<>();
			    			cList.add( (LinearIntegerConstraint)childLeft);
			    			cList.add( (LinearIntegerConstraint)childRight);
			    		} else {
			    			// op instance of Operator
				    		//System.err.println(childTerms.get(1).getClass().getSimpleName());
				    		constraint = new BinaryLinearIntegerExpression((IntegerExpression) childLeft, (Operator) op, (IntegerExpression) childRight);
			    		}
			    	}
			    } else if (childTerms.size() == 1) {
			    	constraint = toExpression(childTerms.get(0));
			    } else if (childTerms.size() == 2 && childTerms.get(0).getText().equals("not")) {
			    	constraint = toNegOperator(childTerms.get(1));
			    	
			    }
			      
			} else if (smtTree instanceof SMTLIBv2Parser.Qual_identiferContext) {
				//System.err.println(smtTree.getText());
				constraint = new SymbolicInteger(((Qual_identiferContext) smtTree).getText());
			} else if (smtTree instanceof SMTLIBv2Parser.Spec_constantContext) {
				//System.err.println(smtTree.getText());
				if (smtTree.getChild(0) instanceof HexadecimalContext) {
					constraint = new IntegerConstant(ArithmeticUtils.BitVecToInteger(new BitVec(smtTree.getChild(0).getText())));
				}
				//constraint = new IntegerConstraint();
			}
			if (constraint == null) {}
				//System.out.println(smtTree.getText() + smtTree.getClass().getSimpleName());
			return constraint;
		}
		
		
		private static Object toExpression(ParserRuleContext smtTree) {
			Object constraint = null;
			//System.err.println(smtTree.getText());
			if (smtTree instanceof TermContext) {
				List<ParserRuleContext> childTerms = new ArrayList<>();
			    for (int i = 0; i < smtTree.getChildCount(); i++) {
			    	if (!(smtTree.getChild(i) instanceof TerminalNodeImpl)) 
			    		childTerms.add((ParserRuleContext) smtTree.getChild(i));
			    }
			    if (childTerms.size() == 3) { // operation 
			    	//System.err.print(toOperator(childTerms.get(0)));
			    	Object op = toOperator(childTerms.get(0));
			    	Object childLeft = toExpression(childTerms.get(1));
		    		Object childRight = toExpression(childTerms.get(2));
		    		if (op instanceof Comparator) {
			    		if (childLeft instanceof IntegerExpression && childRight instanceof IntegerExpression) {
			    			constraint = new LinearIntegerConstraint((IntegerExpression) childLeft, (Comparator) op, (IntegerExpression) childRight);
			    		} else if (childLeft instanceof LinearIntegerConstraint && childRight instanceof LogicalORLinearIntegerConstraints) {
			    			List<Constraint> cList = new ArrayList<>();
			    			cList.add( (Constraint) childLeft);
			    			cList.add( (Constraint) childRight);
			    			constraint = cList;
			    		}
			    		
			    	} else {
			    		if (op == Operator.OR) {
			    			//LogicalORLinearIntegerConstraints 
			    			List<LinearIntegerConstraint> cList = new ArrayList<>();
			    			cList.add( (LinearIntegerConstraint)childLeft);
			    			cList.add( (LinearIntegerConstraint)childRight);
			    			constraint = new LogicalORLinearIntegerConstraints(cList);
			    			//constraint = new BinaryNonLinearIntegerExpression((IntegerExpression) childLeft, (Operator) op, (IntegerExpression) childRight);
			    		} else if (op == Operator.AND) {
			    			List<LinearIntegerConstraint> cList = new ArrayList<>();
			    			cList.add( (LinearIntegerConstraint)childLeft);
			    			cList.add( (LinearIntegerConstraint)childRight);
			    		} else {
			    			// op instance of Operator
				    		//System.err.println(childTerms.get(1).getClass().getSimpleName());
				    		constraint = new BinaryLinearIntegerExpression((IntegerExpression) childLeft, (Operator) op, (IntegerExpression) childRight);
			    		}
			    	}
			    } else if (childTerms.size() == 1) {
			    	constraint = toExpression(childTerms.get(0));
			    } else if (childTerms.size() == 2 && childTerms.get(0).getText().equals("not")) {
			    	constraint = toNotExpression(childTerms.get(1));
			    	
			    }
			      
			} else if (smtTree instanceof SMTLIBv2Parser.Qual_identiferContext) {
				//System.err.println(smtTree.getText());
				constraint = new SymbolicInteger(((Qual_identiferContext) smtTree).getText());
			} else if (smtTree instanceof SMTLIBv2Parser.Spec_constantContext) {
				//System.err.println(smtTree.getText());
				if (smtTree.getChild(0) instanceof HexadecimalContext) {
					constraint = new IntegerConstant(ArithmeticUtils.BitVecToInteger(new BitVec(smtTree.getChild(0).getText())));
				}
				//constraint = new IntegerConstraint();
			}
			if (constraint == null)
				System.out.println(smtTree.getText() + smtTree.getClass().getSimpleName());
			return constraint;
		}
	}
	
	protected class MethodSummary {
        private String methodName = "";
        private String argTypes = "";
        private String argValues = "";
        private String symValues = "";
        private Vector<Pair> pathConditions;

        public MethodSummary() {
            pathConditions = new Vector<Pair>();
        }

        public void setMethodName(String mName) {
            this.methodName = mName;
        }

        public String getMethodName() {
            return this.methodName;
        }

        public void setArgTypes(String args) {
            this.argTypes = args;
        }

        public String getArgTypes() {
            return this.argTypes;
        }

        public void setArgValues(String vals) {
            this.argValues = vals;
        }

        public String getArgValues() {
            return this.argValues;
        }

        public void setSymValues(String sym) {
            this.symValues = sym;
        }

        public String getSymValues() {
            return this.symValues;
        }

        public void addPathCondition(Pair pc) {
            pathConditions.add(pc);
        }

        public Vector<Pair> getPathConditions() {
            return this.pathConditions;
        }

    }
}