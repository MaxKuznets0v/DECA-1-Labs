package analysis.exercise1;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import java.util.*;
import javax.annotation.Nonnull;
import java.util.stream.Stream;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.expr.JInterfaceInvokeExpr;
import sootup.core.jimple.common.expr.JVirtualInvokeExpr;
import sootup.core.model.Body;
import sootup.core.signatures.MethodSignature;
import sootup.core.typehierarchy.TypeHierarchy;
import sootup.core.types.ClassType;
import sootup.java.core.JavaSootClass;
import sootup.java.core.JavaSootMethod;
import sootup.java.core.types.JavaClassType;
import sootup.java.core.views.JavaView;

public class CHAAlgorithm extends CallGraphAlgorithm {

	@Nonnull
	@Override
	protected String getAlgorithm() {
		return "CHA";
	}

	protected void parseMethodStatements(MethodSignature m, @Nonnull JavaView view, @Nonnull CallGraph cg) {
		Optional<JavaSootMethod> sootMethod = view.getMethod(m);
		if (!sootMethod.isPresent()) {
			return;
		}
		
		JavaSootMethod javaSootMethod = sootMethod.get();
		if (!javaSootMethod.hasBody()) {
			return;
		}

		Body body = javaSootMethod.getBody();
		body.getStmts().forEach(stmt -> {
			if (!stmt.containsInvokeExpr()) {
				return;
			}

			AbstractInvokeExpr invokeExpr = stmt.getInvokeExpr();
			MethodSignature innerMethod = invokeExpr.getMethodSignature();
			Set<MethodSignature> potentialMethods = new HashSet<>();
			if (invokeExpr instanceof JVirtualInvokeExpr) {
				MethodSignature implementedCall = getImplementedMethod(innerMethod.getDeclClassType(), innerMethod, view);
				innerMethod = implementedCall;
				potentialMethods.addAll(resolveVirtualCall(innerMethod.getDeclClassType(), implementedCall, view));
			}
			else if (invokeExpr instanceof JInterfaceInvokeExpr) {
				potentialMethods.addAll(resolveVirtualCall(innerMethod.getDeclClassType(), innerMethod, view));
			}
			potentialMethods.add(innerMethod);
			
			for (MethodSignature methodSignature : potentialMethods) {
				if (!cg.hasNode(methodSignature)) {
					cg.addNode(methodSignature);
				}
				if (!cg.hasEdge(m, methodSignature)) {
					cg.addEdge(m, methodSignature);
				}
				parseMethodStatements(methodSignature, view, cg);
			}
		});
	}
	
	protected MethodSignature getImplementedMethod(ClassType type, MethodSignature callMethod, @Nonnull JavaView view) {
		Optional<JavaSootClass> viewClass = view.getClass(type);
		if (!viewClass.isPresent()) {
			return callMethod;
		}
		
		JavaSootClass cl = viewClass.get();
		Optional<JavaSootMethod> classMethod = cl.getMethod(callMethod.getSubSignature());
		if (classMethod.isPresent()) {
			return classMethod.get().getSignature();
		}
		Optional<JavaClassType> parType = cl.getSuperclass();
		if (!parType.isPresent()) {
			return callMethod;
		}
		
		return getImplementedMethod(parType.get(), callMethod, view);
	}
	
	protected Set<MethodSignature> resolveVirtualCall(ClassType type, MethodSignature m, @Nonnull JavaView view) {
		Set<MethodSignature> virtualCalls = new HashSet<>();
		TypeHierarchy hierarchy = view.getTypeHierarchy();
		if (hierarchy.contains(type)) {
			Stream<ClassType> subtypes = hierarchy.subtypesOf(type);
			subtypes.forEach(sub -> {
				MethodSignature sm = view.getIdentifierFactory().getMethodSignature(sub, m.getSubSignature());
				virtualCalls.add(sm);
			});
		}
		return virtualCalls;
	}

	@Override
	protected void populateCallGraph(@Nonnull JavaView view, @Nonnull CallGraph cg) {
		// Your implementation goes here, also feel free to add methods as needed
		// To get your entry points we prepared getEntryPoints(view) in the superclass for you

		// TODO: Verify
		Stream<MethodSignature> methodSignatureStream = getEntryPoints(view);
		methodSignatureStream.forEach(entry -> {
			if (!cg.hasNode(entry)) {
				cg.addNode(entry);
			}
			parseMethodStatements(entry, view, cg);
		});
	}
}
