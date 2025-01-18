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
import sootup.core.jimple.common.ref.JFieldRef;
import sootup.core.jimple.common.ref.JInstanceFieldRef;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.Body;
import sootup.core.model.SootMethod;
import sootup.core.signatures.FieldSignature;
import java.util.Collection;
import java.util.Collections;
import java.util.Optional;
import java.util.Set;

public class Exercise2FlowFunctions extends TaintAnalysisFlowFunctions {

    private final VulnerabilityReporter reporter;

    public Exercise2FlowFunctions(VulnerabilityReporter reporter) {
        this.reporter = reporter;
    }

    static public Optional<DataFlowFact> ResolveCallFlowFunction(Stmt callSite, SootMethod callee, DataFlowFact fact) {
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
                else if (fact.getFieldSignature() != null) {
                    Object methodParam = params.toArray()[i];
                    if (methodParam instanceof Local) {
                        return Optional.of(new DataFlowFact(fact.getFieldSignature()));
                    }
                }
            }
        }
        return Optional.empty();
    }

    static public Optional<DataFlowFact> ResolveCallToReturnFlowFunction(Stmt call) {
        if (call.containsInvokeExpr()) {
            AbstractInvokeExpr invokeExpr = call.getInvokeExpr();
            String methodName = invokeExpr.getMethodSignature().getName();
            if (methodName.contains("getParameter") && call instanceof JAssignStmt) {
                JAssignStmt assignStmt = (JAssignStmt) call;
                Value leftOp = assignStmt.getLeftOp();
                // value assignment (e.g. userId = gerParameter(...))
                if (leftOp instanceof Local) {
                    return Optional.of(new DataFlowFact((Local) leftOp));
                }
                // field store (e.g. obj.f = getParameter(...))
                if (leftOp instanceof JInstanceFieldRef) {
                    JInstanceFieldRef fieldRef = (JInstanceFieldRef) leftOp;
                    return Optional.of(new DataFlowFact(fieldRef.getFieldSignature()));
                }
            }
        }
        return Optional.empty();
    }

    static public Optional<DataFlowFact> ResolveNormalFlowFunction(final Stmt curr, DataFlowFact fact) {
        if (curr instanceof JAssignStmt) {
            JAssignStmt assignStmt = (JAssignStmt) curr;
            boolean isRightOpTainted = assignStmt.getRightOp().equals(fact.getVariable());

            // field store (e.g. obj.f = userId)
            if (isRightOpTainted){
                if (assignStmt.getLeftOp() instanceof JInstanceFieldRef) {
                    JInstanceFieldRef fieldRef = (JInstanceFieldRef) assignStmt.getLeftOp();
                    // Taint the field `obj.f`
                    return Optional.of(new DataFlowFact(fieldRef.getFieldSignature()));
                }
            }

            // field load (e.g. userId = obj.f)
            if (assignStmt.getRightOp() instanceof JInstanceFieldRef) {
                JInstanceFieldRef fieldRef = (JInstanceFieldRef) assignStmt.getRightOp();
                if (fieldRef.getFieldSignature().equals(fact.getFieldSignature())) {
                    LValue leftOp = assignStmt.getLeftOp();
                    if (leftOp instanceof Local) {
                        Local leftVar = (Local) leftOp;
                        return Optional.of(new DataFlowFact(leftVar.withName(leftVar.getName())));
                    }
                }
            }

            // local variable assign (e.g. x = userId)
            if (isRightOpTainted) {
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
        return fact -> {
            if (fact == DataFlowFact.getZeroInstance()) {
                return Collections.emptySet();
            }

            prettyPrint(callSite, fact);
            Set<DataFlowFact> out = Sets.newHashSet();

            //TODO: Implement Exercise 1c) here
            //TODO: Implement interprocedural part of Exercise 2 here
            Optional<DataFlowFact> createdFact = ResolveCallFlowFunction(callSite, callee, fact);
            createdFact.ifPresent(out::add);

            return out;
        };
    }

    public FlowFunction<DataFlowFact> getCallToReturnFlowFunction(final Stmt callSiteStmt, Stmt returnSite) {
        return val -> {

            Set<DataFlowFact> out = Sets.newHashSet();
            out.add(val);
            modelStringOperations(val, out, callSiteStmt);

            if (val == DataFlowFact.getZeroInstance()) {
                //TODO: Implement Exercise 1a) here
                Optional<DataFlowFact> createdFact = ResolveCallToReturnFlowFunction(callSiteStmt);
                createdFact.ifPresent(out::add);
            }

            if (callSiteStmt.toString().contains("executeQuery")) {
                Value arg = callSiteStmt.getInvokeExpr().getArg(0);
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

    @Override
    public FlowFunction<DataFlowFact> getNormalFlowFunction(final Stmt curr, Stmt succ) {
        return fact -> {
            prettyPrint(curr, fact);
            Set<DataFlowFact> out = Sets.newHashSet();
            out.add(fact);

            //TODO: Implement Exercise 1b) here
            Optional<DataFlowFact> createdFact = ResolveNormalFlowFunction(curr, fact);
            createdFact.ifPresent(out::add);
            //TODO: Implement cases for field load and field store statement of Exercise 2) here
            // field store


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
