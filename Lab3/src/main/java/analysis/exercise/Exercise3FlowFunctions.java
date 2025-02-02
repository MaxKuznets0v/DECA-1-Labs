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
import sootup.core.jimple.common.ref.JInstanceFieldRef;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.Body;
import sootup.core.model.SootMethod;

import java.util.Collection;
import java.util.Collections;
import java.util.Optional;
import java.util.Set;

public class Exercise3FlowFunctions extends TaintAnalysisFlowFunctions {

    private final VulnerabilityReporter reporter;

    public Exercise3FlowFunctions(VulnerabilityReporter reporter) {
        this.reporter = reporter;
    }

    @Override
    public FlowFunction<DataFlowFact> getCallFlowFunction(Stmt callSite, SootMethod callee) {
        return fact -> {

            if (fact == DataFlowFact.getZeroInstance()) {
                return Collections.emptySet();
            }

            prettyPrint(callSite, fact);
            Set<DataFlowFact> out = Sets.newHashSet();

            if (callSite.containsInvokeExpr()) {
                AbstractInstanceInvokeExpr invokeExpr = (AbstractInstanceInvokeExpr) callSite.getInvokeExpr();
                Body body = callee.getBody();
                Collection<Local> params = body.getParameterLocals();
                for (int i = 0; i < invokeExpr.getArgCount(); ++i) {
                    Value arg = invokeExpr.getArg(i);
                    if (fact.getVariable().equals(arg)) {
                        Object methodParam = params.toArray()[i];
                        if (methodParam instanceof Local) {
                            if (fact.getFieldSignature() != null) {
                                out.add(new DataFlowFact((Local) methodParam, fact.getFieldSignature()));
                            } else {
                                out.add(new DataFlowFact((Local) methodParam));
                            }
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

            if (val == DataFlowFact.getZeroInstance()) {
                Optional<DataFlowFact> createdFact = Exercise1FlowFunctions.ResolveCallToReturnFlowFunction(call);
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

    private void modelStringOperations(DataFlowFact fact, Set<DataFlowFact> out, Stmt callSiteStmt) {
        handleCallSite(fact, out, callSiteStmt);

        /*For any call x = var.toString(), if the base variable var is tainted, then x is tainted.*/
        if (callSiteStmt instanceof JAssignStmt && callSiteStmt.toString().contains("toString()")) {
            if (callSiteStmt.getInvokeExpr() instanceof AbstractInstanceInvokeExpr) {
                AbstractInstanceInvokeExpr instanceInvokeExpr = (AbstractInstanceInvokeExpr) callSiteStmt.getInvokeExpr();
                if (fact.getVariable().equals(instanceInvokeExpr.getBase())) {
                    Value leftOp = ((JAssignStmt) callSiteStmt).getLeftOp();
                    if (leftOp instanceof Local) {
                        out.add(new DataFlowFact((Local) leftOp));
                    }
                }
            }
        }
    }

    static void handleCallSite(DataFlowFact fact, Set<DataFlowFact> out, Stmt callSiteStmt) {
        if (callSiteStmt instanceof JAssignStmt && callSiteStmt.toString().contains("java.lang.StringBuilder append(") && callSiteStmt.getInvokeExpr() instanceof AbstractInstanceInvokeExpr) {
            Value arg0 = callSiteStmt.getInvokeExpr().getArg(0);
            Value base = ((AbstractInstanceInvokeExpr) callSiteStmt.getInvokeExpr()).getBase();
            /*Does the propagated value match the first parameter of the append call or the base variable*/
            if (fact.getVariable().equals(arg0) || fact.getVariable().equals(base)) {
                /*Yes, then taint the left side of the assignment*/
                Value leftOp = ((JAssignStmt) callSiteStmt).getLeftOp();
                if (leftOp instanceof Local) {
                    out.add(new DataFlowFact((Local) leftOp));
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

            if (curr instanceof JAssignStmt) {
                JAssignStmt assignStmt = (JAssignStmt) curr;
                Value rightOp = assignStmt.getRightOp();
                DataFlowFact rightFact = null;
                if (rightOp instanceof JInstanceFieldRef) {
                    JInstanceFieldRef rightFieldRef = (JInstanceFieldRef) rightOp;
                    rightFact = new DataFlowFact(rightFieldRef.getBase(), rightFieldRef.getFieldSignature());
                }

                if (rightOp.equals(fact.getVariable()) || fact.equals(rightFact)) {
                    LValue leftOp = assignStmt.getLeftOp();
                    if (leftOp instanceof Local) {
                        Local leftVar = (Local)assignStmt.getLeftOp();
                        out.add(new DataFlowFact(leftVar.withName(leftVar.getName())));
                    }
                    if (leftOp instanceof JInstanceFieldRef) {
                        JInstanceFieldRef fieldRef = (JInstanceFieldRef) leftOp;
                        out.add(new DataFlowFact(fieldRef.getBase(), fieldRef.getFieldSignature()));
                    }
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
