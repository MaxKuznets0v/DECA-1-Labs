package analysis;

import com.google.common.collect.Sets;
import heros.DefaultSeeds;
import heros.FlowFunction;
import heros.FlowFunctions;
import heros.InterproceduralCFG;
import heros.flowfunc.Identity;
import heros.solver.Pair;
import sootup.analysis.interprocedural.ifds.DefaultJimpleIFDSTabulationProblem;
import sootup.core.jimple.basic.Immediate;
import sootup.core.jimple.basic.LValue;
import sootup.core.jimple.basic.Local;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.constant.IntConstant;
import sootup.core.jimple.common.expr.*;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.JReturnStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.Body;
import sootup.core.model.SootMethod;
import sootup.core.signatures.MethodSignature;
import sootup.core.types.NullType;
import sootup.java.core.JavaSootMethod;
import sootup.java.core.views.JavaView;
import java.util.*;

public class IFDSLinearConstantAnalysisProblem extends DefaultJimpleIFDSTabulationProblem<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> {
    private final List<MethodSignature> entryPoints;

    protected final JavaView view;

    protected final static int LOWER_BOUND = -1000;

    protected final static int UPPER_BOUND = 1000;

    protected InterproceduralCFG<Stmt, SootMethod> icfg;

    public IFDSLinearConstantAnalysisProblem(List<MethodSignature> entryPoints, JavaView view, InterproceduralCFG<Stmt, SootMethod> icfg) {
        super(icfg);
        this.entryPoints = entryPoints;
        this.view = view;
        this.icfg = icfg;
    }

    @Override
    public Map<Stmt, Set<Pair<Local, Integer>>> initialSeeds() {
        for (MethodSignature methodSignature : entryPoints) {
            SootMethod m = view.getMethod(methodSignature).get();
            if (!m.hasBody()) {
                continue;
            }
            if (m.getName().equals("entryPoint")) {
                return DefaultSeeds.make(Collections.singleton(m.getBody().getStmtGraph().getStartingStmt()), zeroValue());
            }
        }
        throw new IllegalStateException("View does not contain entryPoint " + entryPoints);
    }
    
    boolean IsFactInLinearExpr(AbstractFloatBinopExpr expr, Pair<Local, Integer> fact) {
        Immediate op1 = expr.getOp1();
        Immediate op2 = expr.getOp2();
        String factName = fact.getO1().getName();
        Local op = null;
        if (op1 instanceof Local) {
            op = (Local) op1;
        }
        if (op2 instanceof Local) {
            op = (Local) op2;
        }
        return op != null && op.getName().equals(factName);
    }

    private Optional<Integer> EvaluateAddExpr(JAddExpr addExpr, Pair<Local, Integer> fact) {
        Immediate op1 = addExpr.getOp1();
        Immediate op2 = addExpr.getOp2();
        if (op1 instanceof Local && op2 instanceof IntConstant) {
            IntConstant constant = (IntConstant) op2;
            if (((Local) op1).getName().equals(fact.getO1().getName())) {
                return Optional.of(fact.getO2() + constant.getValue());
            }
        } else if (op2 instanceof Local && op1 instanceof IntConstant) {
            IntConstant constant = (IntConstant) op1;
            if (((Local) op2).getName().equals(fact.getO1().getName())) {
                return Optional.of(fact.getO2() + constant.getValue());
            }
        }
        return Optional.empty();
    }

    private Optional<Integer> EvaluateSubExpr(JSubExpr subExpr, Pair<Local, Integer> fact) {
        Immediate op1 = subExpr.getOp1();
        Immediate op2 = subExpr.getOp2();
        if (op1 instanceof Local && op2 instanceof IntConstant) {
            IntConstant constant = (IntConstant) op2;
            if (((Local) op1).getName().equals(fact.getO1().getName())) {
                return Optional.of(fact.getO2() - constant.getValue());
            }
        } else if (op2 instanceof Local && op1 instanceof IntConstant) {
            IntConstant constant = (IntConstant) op1;
            if (((Local) op2).getName().equals(fact.getO1().getName())) {
                return Optional.of(constant.getValue() - fact.getO2());
            }
        }
        return Optional.empty();
    }

    private Optional<Integer> EvaluateMulExpr(JMulExpr mulExpr, Pair<Local, Integer> fact) {
        Immediate op1 = mulExpr.getOp1();
        Immediate op2 = mulExpr.getOp2();
        if (op1 instanceof Local && op2 instanceof IntConstant) {
            IntConstant constant = (IntConstant) op2;
            if (((Local) op1).getName().equals(fact.getO1().getName())) {
                return Optional.of(fact.getO2() * constant.getValue());
            }
        } else if (op2 instanceof Local && op1 instanceof IntConstant) {
            IntConstant constant = (IntConstant) op1;
            if (((Local) op2).getName().equals(fact.getO1().getName())) {
                return Optional.of(constant.getValue() * fact.getO2());
            }
        }
        return Optional.empty();
    }
    
    private void AddFact(Local local, Integer integer, Set<Pair<Local, Integer>> out) {
        if (integer >= LOWER_BOUND && integer <= UPPER_BOUND) {
            out.add(new Pair<>(local, integer));
        }
    }

    private void AddFact(Pair<Local, Integer> fact, Set<Pair<Local, Integer>> out) {
        AddFact(fact.getO1(), fact.getO2(), out);
    }

    // TODO: You have to implement the FlowFunctions interface.
    // Use Pair<Local, Integer> as type for the data-flow facts.
    @Override
    protected FlowFunctions<Stmt, Pair<Local, Integer>, SootMethod> createFlowFunctionsFactory() {
        return new FlowFunctions<Stmt, Pair<Local, Integer>, SootMethod>() {
            @Override
            public FlowFunction<Pair<Local, Integer>> getNormalFlowFunction(Stmt curr, Stmt next) {
            	return fact -> {
                    Set<Pair<Local, Integer>> out = Sets.newHashSet();
                	if (curr instanceof JAssignStmt) {
                		JAssignStmt assignStmt = (JAssignStmt) curr;
                		Value rightOp = assignStmt.getRightOp();
                		LValue leftOp = assignStmt.getLeftOp();
                		if (leftOp instanceof Local) {
                            Local leftVar = (Local) leftOp;
                            Optional<Integer> rightVal = Optional.empty();
                            
                            if (rightOp instanceof IntConstant) {
                                IntConstant constant = (IntConstant) rightOp;
                                rightVal = Optional.of(constant.getValue());
                            } else if (rightOp instanceof AbstractFloatBinopExpr && 
                                    IsFactInLinearExpr((AbstractFloatBinopExpr) rightOp, fact)) {
                                if (rightOp instanceof JAddExpr) {
                                    rightVal = EvaluateAddExpr((JAddExpr) rightOp, fact);
                                } else if (rightOp instanceof JSubExpr) {
                                    rightVal = EvaluateSubExpr((JSubExpr) rightOp, fact);
                                } else if (rightOp instanceof JMulExpr) {
                                    rightVal = EvaluateMulExpr((JMulExpr) rightOp, fact);
                                }
                            }
                            if (rightVal.isPresent()) {
                                Integer val = rightVal.get();
                                AddFact(leftVar, val, out);
                            }
                		} 
                	}
                    AddFact(fact, out);
                    
					return out;
            	};
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getCallFlowFunction(Stmt callsite, SootMethod dest) {
                // TODO: Implement this flow function factory to map the actual into the formal arguments.
                // Caution, actual parameters may be integer literals as well.
            	return fact -> {
                    if (fact == zeroValue()) {
                        return Collections.emptySet();
                    }
                    
                    Set<Pair<Local, Integer>> out = Sets.newHashSet();

                    if (callsite.containsInvokeExpr()) {
                        AbstractInstanceInvokeExpr invokeExpr = (AbstractInstanceInvokeExpr) callsite.getInvokeExpr();
                        Body body = dest.getBody();
                        Collection<Local> params = body.getParameterLocals();
                        for (int i = 0; i < invokeExpr.getArgCount(); ++i) {
                            Object methodParam = params.toArray()[i];
                            Value arg = invokeExpr.getArg(i);
                            if (methodParam instanceof Local) {
                                if (arg instanceof IntConstant) {
                                    AddFact((Local) methodParam, ((IntConstant) arg).getValue(), out);
                                } else if (arg instanceof Local) {
                                    Local localArg = (Local) arg;
                                    if (localArg.equals(fact.getO1())) {
                                        AddFact((Local) methodParam, fact.getO2(), out);
                                    }
                                }
                            } 
                        }
                    }
                    
					return out;
            	};
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getReturnFlowFunction(Stmt callsite, SootMethod callee, Stmt exit, Stmt retsite) {
                // TODO: Map the return value back into the caller's context if applicable.
                // Since Java has pass-by-value semantics for primitive data types, you do not have to map the formals
                // back to the actuals at the exit of the callee.
                return fact -> {
                    Set<Pair<Local, Integer>> out = Sets.newHashSet();
                    
                    if (callsite instanceof JAssignStmt) {
                        JAssignStmt assignStmt = (JAssignStmt) callsite;
                        LValue leftOp = assignStmt.getLeftOp();
                        if (leftOp instanceof Local) {
                            Local leftLocal = (Local) leftOp;
                            
                            if (exit instanceof JReturnStmt) {
                                JReturnStmt returnStmt = (JReturnStmt) exit;
                                Immediate retIm = returnStmt.getOp();
                                if (retIm instanceof Local) {
                                    if (retIm.equals(fact.getO1())) {
                                        AddFact(leftLocal, fact.getO2(), out);
                                    }
                                }
                            }
                        }
                    }
                    
                    return out;
                };
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getCallToReturnFlowFunction(Stmt callsite, Stmt retsite) {
                // TODO: getCallToReturnFlowFunction can be left to return id in many analysis; this time as well?
                // Restrict your implementation to transfer only the data-flow facts that are not involved in a call.
                return Identity.v();
            }
        };
    }


    @Override
    protected Pair<Local, Integer> createZeroValue() {
        return new Pair<>(new Local("<<zero>>", NullType.getInstance()), Integer.MIN_VALUE);
    }

}
