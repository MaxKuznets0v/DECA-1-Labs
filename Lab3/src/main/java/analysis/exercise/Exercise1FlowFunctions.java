package analysis.exercise;

import analysis.TaintAnalysisFlowFunctions;
import analysis.VulnerabilityReporter;
import analysis.fact.DataFlowFact;
import com.google.common.collect.Sets;
import heros.FlowFunction;
import sootup.core.jimple.basic.LValue;
import sootup.core.jimple.basic.Local;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.expr.AbstractInstanceInvokeExpr;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.Body;
import sootup.core.model.SootMethod;

import java.util.Collection;
import java.util.Collections;
import java.util.Optional;
import java.util.Set;

public class Exercise1FlowFunctions extends TaintAnalysisFlowFunctions {

    private final VulnerabilityReporter reporter;

    public Exercise1FlowFunctions(VulnerabilityReporter reporter) {
        this.reporter = reporter;
    }

    // Implements Exercise 1c)
    static public Optional<DataFlowFact> ResolveCodeFlowFunction(Stmt callSite, SootMethod callee, DataFlowFact fact) {
        if (callSite.containsInvokeExpr()) {
            AbstractInstanceInvokeExpr invokeExpr = (AbstractInstanceInvokeExpr) callSite.getInvokeExpr();
            Body body = callee.getBody();
            Collection<Local> params = body.getParameterLocals();
            for (int i = 0; i < invokeExpr.getArgCount(); ++i) {
                Value arg = invokeExpr.getArg(i);
                if (fact.getVariable().equals(arg)) {
                    Object methodParam = params.toArray()[i];
                    if (methodParam instanceof Local) {
                        return Optional.of(new DataFlowFact((Local) methodParam));
                    }
                }
            }
        }
        return Optional.empty();
    }

    // Implements Exercise 1a)
    static public Optional<DataFlowFact> ResolveCallToReturnFlowFunction(Stmt call) {
        if (call.containsInvokeExpr()) {
            AbstractInvokeExpr invokeExpr = call.getInvokeExpr();
            String methodName = invokeExpr.getMethodSignature().getName();
            if (methodName.contains("getParameter") && call instanceof JAssignStmt) {
                JAssignStmt assignStmt = (JAssignStmt) call;
                Value leftOp = assignStmt.getLeftOp();
                if (leftOp instanceof Local) {
                    return Optional.of(new DataFlowFact((Local) leftOp));
                }
            }
        }
        return Optional.empty();
    }

    // Implements Exercise 1b)
    static public Optional<DataFlowFact> ResolveNormalFlowFunction(final Stmt curr, DataFlowFact fact) {
        if (curr instanceof JAssignStmt) {
            JAssignStmt assignStmt = (JAssignStmt) curr;
            if (assignStmt.getRightOp().equals(fact.getVariable())) {
                LValue leftOp = assignStmt.getLeftOp();
                if (leftOp instanceof Local) {
                    Local leftVar = (Local) leftOp;
                    return Optional.of(new DataFlowFact(leftVar.withName(leftVar.getName())));
                }
            }
        }
        return Optional.empty();
    }

    @Override
    public FlowFunction<DataFlowFact> getCallFlowFunction(Stmt callSite, SootMethod callee) {
        // returns a function with 1 DataFlow as an input that's once applied..
        // will return a set of DataFlowFact's for the called method/function.
        // e.g. x = fun(y); where y is tainted and fun(String z){}.
        // once the FlowFunction is applied, it will return {z}
        return fact -> {
            System.out.println("Calling: getCallFlowFunction");
            if (fact.equals(DataFlowFact.getZeroInstance()))
                return Collections.emptySet();
            prettyPrint(callSite, fact);
            Set<DataFlowFact> out = Sets.newHashSet();

            Optional<DataFlowFact> createdFact = ResolveCodeFlowFunction(callSite, callee, fact);
            createdFact.ifPresent(out::add);
            return out;
        };
    }

    public FlowFunction<DataFlowFact> getCallToReturnFlowFunction(final Stmt call, Stmt returnSite) {
        return val -> {
            System.out.println("Calling: getCallToReturnFunction");
            Set<DataFlowFact> out = Sets.newHashSet();
            out.add(val);
            modelStringOperations(val, out, call);

            if (val.equals(DataFlowFact.getZeroInstance())) {
                Optional<DataFlowFact> createdFact = ResolveCallToReturnFlowFunction(call);
                createdFact.ifPresent(out::add);
            }
            if (call.toString().contains("executeQuery")) {
                Value arg = call.getInvokeExpr().getArg(0);
                if (val.getVariable().equals(arg)) {
                    reporter.reportVulnerability();
                }
            }
            return out;
        };
    }

    private void modelStringOperations(DataFlowFact fact, Set<DataFlowFact> out,
                                       Stmt callSiteStmt) {
        Exercise3FlowFunctions.handleCallSite(fact, out, callSiteStmt);


        /*For any call x = var.toString(), if the base variable var is tainted, then x is tainted.*/
        if (callSiteStmt instanceof JAssignStmt && callSiteStmt.toString().contains("toString()")) {
            if (callSiteStmt.getInvokeExpr() instanceof AbstractInstanceInvokeExpr) {
                AbstractInstanceInvokeExpr AbstractInstanceInvokeExpr = (AbstractInstanceInvokeExpr) callSiteStmt.getInvokeExpr();
                if (fact.getVariable().equals(AbstractInstanceInvokeExpr.getBase())) {
                    Value leftOp = ((JAssignStmt) callSiteStmt).getLeftOp();
                    if (leftOp instanceof Local) {
                        out.add(new DataFlowFact((Local) leftOp));
                    }
                }
            }
        }
    }

    @Override
    public FlowFunction<DataFlowFact> getNormalFlowFunction(final Stmt curr, Stmt succ) {
        // returns a function that takes as an input a single DataFlowFact. once this function is applied,
        // it will return a set of DataFlowFact's generated.
        // e.g. x = a, where a is tainted.
        // once the FlowFunction is applied, the output would be a set containing {x, a}
        return fact -> {
            System.out.println("Calling: getNormalFlowFunction");
            prettyPrint(curr, fact);
            Set<DataFlowFact> out = Sets.newHashSet();
            out.add(fact);

            Optional<DataFlowFact> createdFact = ResolveNormalFlowFunction(curr, fact);
            createdFact.ifPresent(out::add);
            return out;
        };
    }

    @Override
    public FlowFunction<DataFlowFact> getReturnFlowFunction(Stmt callSite, SootMethod callee, Stmt exitStmt, Stmt retSite) {
        return fact -> {
            System.out.println("Calling: getReturnFlowFunction");
            prettyPrint(callSite, fact);
            return Collections.emptySet();
        };
    }
}
