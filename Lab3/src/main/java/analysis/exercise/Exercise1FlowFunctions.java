package analysis.exercise;

import analysis.TaintAnalysisFlowFunctions;
import analysis.VulnerabilityReporter;
import analysis.fact.DataFlowFact;
import com.google.common.collect.Sets;
import heros.FlowFunction;
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
import java.util.Set;

public class Exercise1FlowFunctions extends TaintAnalysisFlowFunctions {

    private final VulnerabilityReporter reporter;

    public Exercise1FlowFunctions(VulnerabilityReporter reporter) {
        this.reporter = reporter;
    }

    @Override
    public FlowFunction<DataFlowFact> getCallFlowFunction(Stmt callSite, SootMethod callee) {
        return fact -> {
            if (fact.equals(DataFlowFact.getZeroInstance()))
                return Collections.emptySet();
            prettyPrint(callSite, fact);
            Set<DataFlowFact> out = Sets.newHashSet();

            //TODO: Implement Exercise 1c) here

            if (callSite.containsInvokeExpr()) {
                AbstractInstanceInvokeExpr invokeExpr = (AbstractInstanceInvokeExpr) callSite.getInvokeExpr();
                Body body = callee.getBody();
                Collection<Local> params = body.getParameterLocals();
                for (int i = 0; i < invokeExpr.getArgCount(); ++i) {
                    Value arg = invokeExpr.getArg(i);
                    if (fact.getVariable().equals(arg)) {
                        Object methodParam = params.toArray()[i];
                        if (methodParam instanceof Local) {
                            out.add(new DataFlowFact((Local) methodParam));
                        }
                    }
                }
            }
            return out;
        };
    }

    public FlowFunction<DataFlowFact> getCallToReturnFlowFunction(final Stmt call, Stmt returnSite) {
        return val -> {

            Set<DataFlowFact> out = Sets.newHashSet();
            out.add(val);
            modelStringOperations(val, out, call);

            if (val.equals(DataFlowFact.getZeroInstance())) {

                //TODO: Implement Exercise 1a) here

                if (call.containsInvokeExpr()) {
                    AbstractInvokeExpr invokeExpr = call.getInvokeExpr();
                    String methodName = invokeExpr.getMethodSignature().getName();
                    if (methodName.contains("getParameter") && call instanceof JAssignStmt) {
                        JAssignStmt assignStmt = (JAssignStmt) call;
                        Value leftOp = assignStmt.getLeftOp();
                        if (leftOp instanceof Local) {
                            out.add(new DataFlowFact((Local) leftOp));
                        }
                    }
                }
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
        return fact -> {
            prettyPrint(curr, fact);
            Set<DataFlowFact> out = Sets.newHashSet();
            out.add(fact);

            //TODO: Implement Exercise 1b) here

            if (curr instanceof JAssignStmt) {
                JAssignStmt assignStmt = (JAssignStmt) curr;
                if (assignStmt.getRightOp().equals(fact.getVariable())) {
                    Local leftVar = (Local) assignStmt.getLeftOp();
                    out.add(new DataFlowFact(leftVar.withName(leftVar.getName())));
                }
            }
            return out;
        };
    }

    @Override
    public FlowFunction<DataFlowFact> getReturnFlowFunction(Stmt callSite, SootMethod callee, Stmt exitStmt, Stmt retSite) {
        return fact -> {
            prettyPrint(callSite, fact);
            return Collections.emptySet();
        };
    }
}
