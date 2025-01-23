package analysis;

import heros.*;
import heros.edgefunc.AllBottom;
import heros.edgefunc.EdgeIdentity;
import heros.flowfunc.Identity;
import sootup.analysis.interprocedural.ide.DefaultJimpleIDETabulationProblem;
import sootup.core.jimple.basic.Local;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootMethod;
import sootup.core.signatures.MethodSignature;
import sootup.core.types.NullType;
import sootup.java.core.views.JavaView;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class IDELinearConstantAnalysisProblem extends DefaultJimpleIDETabulationProblem<Local, Integer, InterproceduralCFG<Stmt, SootMethod>> {

    protected InterproceduralCFG<Stmt, SootMethod> icfg;
    private final List<MethodSignature> entryPoints;

    protected final JavaView view;


    private final static EdgeFunction<Integer> ALL_BOTTOM = new AllBottom<>(Integer.MAX_VALUE);

    protected final static Integer TOP = Integer.MIN_VALUE;

    protected final static Integer BOTTOM = Integer.MAX_VALUE;

    private int executeBinOperation(String op, int lhs, int rhs) {
        int res;
        switch (op.trim()) {
            case "+":
                res = lhs + rhs;
                break;
            case "-":
                res = lhs - rhs;
                break;
            case "*":
                res = lhs * rhs;
                break;
            case "/":
                res = lhs / rhs;
                break;
            case "%":
                res = lhs % rhs;
                break;
            default:
                throw new UnsupportedOperationException("Could not execute unknown operation '" + op + "'!");
        }
        return res;
    }

    public IDELinearConstantAnalysisProblem(InterproceduralCFG<Stmt, SootMethod> icfg, List<MethodSignature> entryPoints, JavaView view) {
        super(icfg);
        this.icfg = icfg;
        this.entryPoints = entryPoints;
        this.view = view;
    }

    protected static class EdgeFunctionComposer implements EdgeFunction<Integer> {

        private final EdgeFunction<Integer> F;
        private final EdgeFunction<Integer> G;

        public EdgeFunctionComposer(EdgeFunction<Integer> F, EdgeFunction<Integer> G) {
            this.F = F;
            this.G = G;
        }

        @Override
        public Integer computeTarget(Integer source) {
            return F.computeTarget(G.computeTarget(source));
        }

        @Override
        public EdgeFunction<Integer> composeWith(EdgeFunction<Integer> secondFunction) {
            return G.composeWith(F.composeWith(secondFunction));
        }

        @Override
        public EdgeFunction<Integer> meetWith(EdgeFunction<Integer> otherFunction) {
            // FIXME: needs improvement, but is good enough to analyze the current target programs
            if (this == ALL_BOTTOM && otherFunction != ALL_BOTTOM) {
                return otherFunction;
            } else if (this != ALL_BOTTOM && otherFunction == ALL_BOTTOM) {
                return this;
            } else {
                return this;
            }
        }

        @Override
        public boolean equalTo(EdgeFunction<Integer> other) {
            return F.equalTo(other);
        }

    }

    @Override
    protected EdgeFunction<Integer> createAllTopFunction() {


        // TODO: Implement this function to return a special EdgeFunction that
        // represents 'no information', that is used to initialize the data-flow
        // fact's values.

        return null;
    }

    // TODO: Implement this MeetLattice factory function, to return the lattice
    // for your data-flow analysis. The MeetLattice implementation states what
    // the top and bottom element are in your analysis's underlying lattice.
    // Additionally it states how to make two values in the lattice meet.
    // It probably makes sense to have an additional global variable in this
    // description class that represents the BOTTOM element; that will surely
    // become handy for the implementation of the EdgeFunctions.
    @Override
    protected MeetLattice<Integer> createMeetLattice() {
        return new MeetLattice<Integer>() {
            @Override
            public Integer topElement() {
                return null;
            }

            @Override
            public Integer bottomElement() {
                return null;
            }

            @Override
            public Integer meet(Integer left, Integer right) {
                return null;
            }
        };
    }

    // TODO: You have to implement the FlowFunctions interface.
    // This is very similar to the IFDS analysis, but this time your just use
    // Local as type of the data-flow facts. Do not worry about a Local's value
    // here (the EdgeFunctions will take care of this job), just generate and
    // kill constant Locals when adequate.
    @Override
    protected FlowFunctions<Stmt, Local, SootMethod> createFlowFunctionsFactory() {
        return new FlowFunctions<Stmt, Local, SootMethod>() {
            @Override
            public FlowFunction<Local> getNormalFlowFunction(Stmt curr, Stmt succ) {
                // TODO: Implement this flow function factory to obtain an intra-procedural data-flow analysis.
                return Identity.v();
            }

            @Override
            public FlowFunction<Local> getCallFlowFunction(Stmt callStmt, SootMethod dest) {
                // TODO: Implement this flow function factory to map the actual into the formal arguments.
                // Caution, actual parameters may be integer literals as well.
                return Identity.v();
            }

            @Override
            public FlowFunction<Local> getReturnFlowFunction(Stmt callSite, SootMethod calleeMethod, Stmt exitStmt, Stmt returnSite) {
                // TODO: Map the return value back into the caller's context if applicable.
                // Since Java has pass-by-value semantics for primitive data types, you do not have to map the formals
                // back to the actuals at the exit of the callee.
                return Identity.v();
            }

            @Override
            public FlowFunction<Local> getCallToReturnFlowFunction(Stmt callSite, Stmt returnSite) {
                // TODO: getCallToReturnFlowFunction can be left to return id in many analysis; this time as well?
                return Identity.v();
            }
        };
    }

    // TODO: You have to implement the EdgeFunctions interface.
    // The EdgeFunctions take care of the actual value computation within this
    // linear constant propagation. An EdgeFunction is basically the
    // non-evaluated function representation of a constant Integer value
    // (or better its computation).
    // Similar to the FlowFunctions you may return different EdgeFunctions
    // depending on the current statement you are looking at.
    // An EdgeFunction describes an IDE lambda function on an exploded
    // super-graph edge from 'srcNode' to 'tgtNode', for instance, when looking
    // at 'getNormalEdgeFunction'. Do you have to implement all EdgeFunction
    // factory methods for the linear constant propagation?
    // Before you start, let us clarify the EdgeFunction interface:
    //        public interface EdgeFunction<V> {
    //          // This is where the magic happens and the most important
    //          // function of this interface. In compute targets your encode
    //          // the actual lambda function that describes what operation is
    //          // performed on an incoming Integer. This function can for
    //          // instance return a number, pass it as identity or perform
    //          // further arithmetic operations on it.
    //          V computeTarget(V source);
    //          // In composeWith you are able to describe how two EdgeFunctions
    //          // can be composed with each other. You probably would like to
    //          // create a new class implementing the EdgeFunction interface
    //          // and is able compose two EdgeFunctions.
    //          EdgeFunction<V> composeWith(EdgeFunction<V> secondFunction);
    //          // As the name suggests this function states how two
    //          // EdgeFunctions have to be met. Remember that EdgeFunctions
    //          // are non-evaluated constant values.
    //          EdgeFunction<V> meetWith(EdgeFunction<V> otherFunction);
    //          // This function tells if 'this' EdgeFunction and the 'other'
    //          // EdgeFunction are equal.
    //          public boolean equalTo(EdgeFunction<V> other);
    //        }
    // Happy data-flow analysis ;-)
    @Override
    protected EdgeFunctions<Stmt, Local, SootMethod, Integer> createEdgeFunctionsFactory() {
        return new EdgeFunctions<Stmt, Local, SootMethod, Integer>() {
            @Override
            public EdgeFunction<Integer> getNormalEdgeFunction(Stmt src, Local srcNode, Stmt tgt, Local tgtNode) {
                return EdgeIdentity.v();
            }

            @Override
            public EdgeFunction<Integer> getCallEdgeFunction(Stmt callStmt, Local srcNode, SootMethod destinationMethod, Local destNode) {
                return EdgeIdentity.v();
            }

            @Override
            public EdgeFunction<Integer> getReturnEdgeFunction(Stmt callSite, SootMethod calleeMethod, Stmt exitStmt, Local exitNode, Stmt returnSite, Local retNode) {
                return EdgeIdentity.v();
            }

            @Override
            public EdgeFunction<Integer> getCallToReturnEdgeFunction(Stmt callStmt, Local callNode, Stmt returnSite, Local returnSideNode) {
                return EdgeIdentity.v();
            }
        };
    }

    @Override
    protected Local createZeroValue() {
        return new Local("<<zero>>", NullType.getInstance());
    }

    @Override
    public Map<Stmt, Set<Local>> initialSeeds() {
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

}
