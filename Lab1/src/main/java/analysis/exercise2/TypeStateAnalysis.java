package analysis.exercise2;

import analysis.FileStateFact;
import analysis.ForwardAnalysis;
import analysis.VulnerabilityReporter;

import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import sootup.core.jimple.basic.Local;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.expr.JSpecialInvokeExpr;
import sootup.core.jimple.common.expr.JVirtualInvokeExpr;
import sootup.core.jimple.common.ref.JStaticFieldRef;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.JInvokeStmt;
import sootup.core.jimple.common.stmt.JReturnVoidStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.signatures.MethodSignature;
import sootup.java.core.JavaSootMethod;

import javax.annotation.Nonnull;

public class TypeStateAnalysis extends ForwardAnalysis<Set<FileStateFact>> {

	public TypeStateAnalysis(@Nonnull JavaSootMethod method, @Nonnull VulnerabilityReporter reporter) {
		super(method, reporter);
		// System.out.println(method.getBody());
	}

	@Override
	protected void flowThrough(@Nonnull Set<FileStateFact> in, @Nonnull Stmt stmt, @Nonnull Set<FileStateFact> out) {
		// TODO: Implement your flow function here.
		copy(in, out);
		if (stmt.containsInvokeExpr()){
			AbstractInvokeExpr invokeExpr = stmt.getInvokeExpr();
			boolean isFileMethod = invokeExpr.getMethodSignature().getDeclClassType().toString().equals("target.exercise2.File");

			if (isFileMethod) {
				// if method is init, add a new fact to set
				if (stmt.getInvokeExpr() instanceof JSpecialInvokeExpr) {
					FileStateFact fact = new FileStateFact(FileStateFact.FileState.Init);
					Value obj = ((JSpecialInvokeExpr) invokeExpr).getBase();
					fact.addAlias(obj);
					out.add(fact);
				}
				// if method is open/close, update fact
				else {
					for(FileStateFact fact : out){
						if (fact.containsAlias(((JVirtualInvokeExpr) invokeExpr).getBase())){
							if (invokeExpr.getMethodSignature().getName().equals("open"))
								fact.updateState(FileStateFact.FileState.Open);
							else if (invokeExpr.getMethodSignature().getName().equals("close"))
								fact.updateState(FileStateFact.FileState.Close);
							break;
						}
					}
				}
			}
		}

		// check for aliasing, add to fact if an obj aliases another
		if (stmt instanceof JAssignStmt) {
			for (FileStateFact fact : out) {
				if (fact.containsAlias(((JAssignStmt) stmt).getRightOp()))
					fact.addAlias((((JAssignStmt) stmt).getLeftOp()));
			}
		}


		prettyPrint(in, stmt, out);

		// report a vulnerability when still open calls are at the end
		if(stmt.toString().equals("return")) {
			for (FileStateFact fact : in)
				if (fact.getState() == FileStateFact.FileState.Open) {
					this.reporter.reportVulnerability(method.getSignature(), stmt);
					break;
				}
		}

	}

	@Nonnull
	@Override
	protected Set<FileStateFact> newInitialFlow() {
		// TODO: Implement your initialization here.
		// The following line may be just a place holder, check for yourself if
		// it needs some adjustments.
		return new HashSet<>();
	}

	@Override
	protected void copy(@Nonnull Set<FileStateFact> source, @Nonnull Set<FileStateFact> dest) {
		// TODO: Implement the copy function here.
		for (FileStateFact fsf : source) {
			dest.add(new FileStateFact(fsf));
		}
	}

	@Override
	protected void merge(@Nonnull Set<FileStateFact> in1, @Nonnull Set<FileStateFact> in2, @Nonnull Set<FileStateFact> out) {
		// TODO: Implement the merge function here.
	}

}
