package analysis;

import heros.DefaultSeeds;
import heros.FlowFunction;
import heros.FlowFunctions;
import heros.InterproceduralCFG;
import heros.flowfunc.Identity;
import heros.solver.Pair;
import sootup.analysis.interprocedural.ifds.DefaultJimpleIFDSTabulationProblem;
import sootup.core.jimple.basic.LValue;
import sootup.core.jimple.basic.Local;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.constant.IntConstant;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootMethod;
import sootup.core.signatures.MethodSignature;
import sootup.core.types.NullType;
import sootup.java.core.views.JavaView;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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


    // TODO: You have to implement the FlowFunctions interface.
    // Use Pair<Local, Integer> as type for the data-flow facts.
    @Override
    protected FlowFunctions<Stmt, Pair<Local, Integer>, SootMethod> createFlowFunctionsFactory() {
        return new FlowFunctions<Stmt, Pair<Local, Integer>, SootMethod>() {
            @Override
            public FlowFunction<Pair<Local, Integer>> getNormalFlowFunction(Stmt curr, Stmt next) {
                // TODO: Implement this flow function factory to obtain an intra-procedural data-flow analysis.
//            	System.out.println("curr stmt: " + curr);
            	return fact -> {
            		Set<Pair<Local, Integer>> pair = new HashSet<>(Collections.singleton(fact));
                	if (curr instanceof JAssignStmt) {
                		JAssignStmt assignStmt = (JAssignStmt) curr;
                		Value rightOp = assignStmt.getRightOp();
                		LValue leftOp = assignStmt.getLeftOp();
                		if (leftOp instanceof Local && rightOp instanceof IntConstant) {
                			IntConstant constant = (IntConstant) rightOp;
                			Local variable = (Local) leftOp;
                    		pair.add(new Pair<Local, Integer>(variable, constant.getValue()));
                		} 
                	}
					return pair;
            	};
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getCallFlowFunction(Stmt callsite, SootMethod dest) {
                // TODO: Implement this flow function factory to map the actual into the formal arguments.
                // Caution, actual parameters may be integer literals as well.
            	return fact -> {
            		Set<Pair<Local, Integer>> pair = new HashSet<>(Collections.singleton(fact));
//            		if (callsite instanceof JInvokeStmt) {
            			System.out.println("Callsite : " + callsite.getInvokeExpr());
//            		}
					return pair;
            	};
//                return Identity.v();
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getReturnFlowFunction(Stmt callsite, SootMethod callee, Stmt exit, Stmt retsite) {
                // TODO: Map the return value back into the caller's context if applicable.
                // Since Java has pass-by-value semantics for primitive data types, you do not have to map the formals
                // back to the actuals at the exit of the callee.
                return Identity.v();
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getCallToReturnFlowFunction(Stmt callsite, Stmt retsite) {
                // TODO: getCallToReturnFlowFunction can be left to return id in many analysis; this time as well?
                return Identity.v();
            }
        };
    }


    @Override
    protected Pair<Local, Integer> createZeroValue() {
        return new Pair<>(new Local("<<zero>>", NullType.getInstance()), Integer.MIN_VALUE);
    }

}
