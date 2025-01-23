package test.exercises;

import heros.InterproceduralCFG;
import heros.solver.Pair;
import org.junit.Test;
import sootup.analysis.interprocedural.ide.JimpleIDESolver;
import sootup.core.jimple.basic.Local;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootMethod;
import target.exercise1and2.*;
import test.base.IDETestSetUp;

import java.util.ArrayList;
import java.util.List;

public class Exercise2Test extends IDETestSetUp {

    @Test
    public void SimpleAssignment() {
        JimpleIDESolver<Local, Integer, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment2() {
        JimpleIDESolver<Local, Integer, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        expected.add(new Pair<>("k", 40));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment3() {
        JimpleIDESolver<Local, Integer, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment3.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
//        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        expected.add(new Pair<>("k", 400));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment4() {
        JimpleIDESolver<Local, Integer, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment4.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
//        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        expected.add(new Pair<>("k", 413));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment5() {
        JimpleIDESolver<Local, Integer, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment5.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("i#1", 13));
        expected.add(new Pair<>("j", 200));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void FunctionCall2() {
        JimpleIDESolver<Local, Integer, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(FunctionCall2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        expected.add(new Pair<>("k", 101));
        expected.add(new Pair<>("l", 201));
        checkResultsAtLastStatement(analysis, expected);
    }
}
