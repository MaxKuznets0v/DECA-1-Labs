package test.exercises;

import heros.InterproceduralCFG;
import heros.solver.Pair;
import org.junit.Test;
import sootup.analysis.interprocedural.ifds.JimpleIFDSSolver;
import sootup.core.jimple.basic.Local;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootMethod;
import target.exercise1and2.*;
import test.base.IFDSTestSetUp;

import java.util.ArrayList;
import java.util.List;

public class Exercise1Test extends IFDSTestSetUp {

    @Test
    public void SimpleAssignment() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment2() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        expected.add(new Pair<>("k", 40));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment3() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment3.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
//        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        expected.add(new Pair<>("k", 400));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment4() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment4.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
//        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        expected.add(new Pair<>("k", 413));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment5() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment5.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("j", 200));
        expected.add(new Pair<>("i#1", 13));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void Branching() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(Branching.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("i#0", 0));
        expected.add(new Pair<>("i#1", 10));
        expected.add(new Pair<>("j", 1));
        expected.add(new Pair<>("k", 14));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void Branching2() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(Branching2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("i", 0));
        expected.add(new Pair<>("j#0", 0));
        expected.add(new Pair<>("j#1", 42));
        expected.add(new Pair<>("k", 13));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void Loop() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(Loop.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("sum", 1000));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void Loop2() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(Loop2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("sum", 1000));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void FunctionCall() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(FunctionCall.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        expected.add(new Pair<>("k", 300));
        expected.add(new Pair<>("l", 400));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void FunctionCall2() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(FunctionCall2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        expected.add(new Pair<>("k", 101));
        expected.add(new Pair<>("l", 201));
        checkResultsAtLastStatement(analysis, expected);
    }
//

    @Test
    public void FunctionCall3() {
        JimpleIFDSSolver<Pair<Local, Integer>, InterproceduralCFG<Stmt, SootMethod>> analysis = executeStaticAnalysis(FunctionCall3.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair<>("i", 100));
        expected.add(new Pair<>("j", 200));
        expected.add(new Pair<>("k", 113));
        expected.add(new Pair<>("l", 55));
        checkResultsAtLastStatement(analysis, expected);
    }

}
