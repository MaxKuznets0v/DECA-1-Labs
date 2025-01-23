package test.base;

import analysis.IFDSLinearConstantAnalysisProblem;
import heros.InterproceduralCFG;
import heros.solver.Pair;
import sootup.analysis.interprocedural.icfg.JimpleBasedInterproceduralCFG;
import sootup.analysis.interprocedural.ifds.JimpleIFDSSolver;
import sootup.core.jimple.basic.Local;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootMethod;
import sootup.core.signatures.MethodSignature;
import sootup.core.types.ClassType;
import sootup.java.core.JavaSootClass;

import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.Assert.assertEquals;

public abstract class IFDSTestSetUp extends TestSetup {

    protected SootMethod getEntryPointMethod() {
        return entryPointMethod;
    }

    protected JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> executeStaticAnalysis(String targetTestClassName) {

        final ClassType classType = view.getIdentifierFactory().getClassType(targetTestClassName);
        final Optional<JavaSootClass> aClass = view.getClass(classType);
        if (!aClass.isPresent()) {
            throw new IllegalArgumentException("Entrypoint class is not in the View.");
        }
        entryPointMethod = aClass.get().getMethods().stream().filter(SootMethod::hasBody).filter(ms -> ms.getName().equals("entryPoint")).findAny().get();
        final List<MethodSignature> entryPoints = Collections.singletonList(entryPointMethod.getSignature());
        JimpleBasedInterproceduralCFG icfg = new JimpleBasedInterproceduralCFG(view, entryPointMethod.getSignature(), false, false);

        IFDSLinearConstantAnalysisProblem problem = new IFDSLinearConstantAnalysisProblem(entryPoints, view, icfg);
        @SuppressWarnings({"rawtypes", "unchecked"})
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> solver = new JimpleIFDSSolver(problem);
        solver.solve();
        return solver;
    }

    protected void checkResultsAtLastStatement(JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis, List<Pair<String, Integer>> expectedResult) {
        SootMethod m = getEntryPointMethod();
        final List<Stmt> stmtList = m.getBody().getStmts();
        Set<Pair<Local, Integer>> res = analysis.ifdsResultsAt(stmtList.get(stmtList.size() - 1));
        int correctResultCounter = 0;
        for (Pair<String, Integer> expected : expectedResult) {
            for (Pair<Local, Integer> resEntry : res) {
                final String expectedName = expected.getO1();
                final String resName = resEntry.getO1().getName();
                final int expectedValue = expected.getO2();
                final int resValue = resEntry.getO2();
                if (expectedName.equals(resName) && expectedValue == resValue) {
                    correctResultCounter++;
                }
            }
        }
        // FIXME
        if (expectedResult.size() != correctResultCounter) {
            System.out.println(res);
        }
        assertEquals("results are not complete or correct - found", expectedResult.size(), correctResultCounter);
    }

}
