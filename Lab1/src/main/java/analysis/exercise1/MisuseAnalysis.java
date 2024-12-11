package analysis.exercise1;

import analysis.AbstractAnalysis;
import analysis.VulnerabilityReporter;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import sootup.core.jimple.basic.Immediate;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.constant.StringConstant;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.expr.JStaticInvokeExpr;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootClass;
import sootup.core.model.SootMethod;
import sootup.core.signatures.MethodSignature;
import sootup.core.types.ClassType;
import sootup.core.types.Type;
import sootup.java.core.JavaSootMethod;

public class MisuseAnalysis extends AbstractAnalysis {
	public MisuseAnalysis(@Nonnull JavaSootMethod method, @Nonnull VulnerabilityReporter reporter) {
		super(method, reporter);
	}

	@Override
	protected void flowThrough(@Nonnull Stmt stmt) {
		if (!stmt.containsInvokeExpr()) {
			return;
		}

		MethodSignature methodSignature = stmt.getInvokeExpr().getMethodSignature();
		String methodClassName = methodSignature.getDeclClassType().toString();
		String targetClassName = "javax.crypto.Cipher";
		if (!methodClassName.equals(targetClassName)) {
			return;
		}

		String methodName = methodSignature.getName();
		String targetMethodName = "getInstance";
		if (!methodName.equals(targetMethodName)) {
			return;
		}

		List<Type> methodArgs = methodSignature.getParameterTypes();
		if (methodArgs.isEmpty() || !methodArgs.get(0).toString().equals("java.lang.String")) {
			return;
		}

		List<Immediate> stmtArgs = stmt.getInvokeExpr().getArgs();
		if (stmtArgs.isEmpty()) {
			return;
		}

		if (!(stmtArgs.get(0) instanceof StringConstant)) {
			return;
		}

		StringConstant transformation = (StringConstant) stmtArgs.get(0);
		String targetTransformation = "AES/GCM/PKCS5Padding";
		if (transformation.getValue().equals(targetTransformation)) {
			return;
		}

		reporter.reportVulnerability(method.getSignature(), stmt);
	}
}
