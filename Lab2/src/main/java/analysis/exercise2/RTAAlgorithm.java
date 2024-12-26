package analysis.exercise2;

import analysis.CallGraph;
import analysis.exercise1.CHAAlgorithm;
import javax.annotation.Nonnull;

import org.checkerframework.checker.nullness.qual.NonNull;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.expr.JInterfaceInvokeExpr;
import sootup.core.jimple.common.expr.JVirtualInvokeExpr;
import sootup.core.jimple.common.expr.JNewExpr;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.model.Body;
import sootup.core.signatures.MethodSignature;
import sootup.core.typehierarchy.TypeHierarchy;
import sootup.core.types.ClassType;
import sootup.java.core.JavaSootClass;
import sootup.java.core.JavaSootMethod;
import sootup.java.core.views.JavaView;

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

public class RTAAlgorithm extends CHAAlgorithm {

  protected final Set<ClassType> instantiatedClasses = new HashSet<>();

  @Override
  protected Set<MethodSignature> resolveVirtualCall(ClassType type, MethodSignature m, @Nonnull JavaView view) {
    Set<MethodSignature> virtualCalls = new HashSet<>();
    TypeHierarchy hierarchy = view.getTypeHierarchy();
    if (hierarchy.contains(type)) {
      Stream<ClassType> subtypes = hierarchy.subtypesOf(type);
      System.out.println("Subtypes: " + subtypes);
      subtypes.forEach(sub -> {
        if (instantiatedClasses.contains(sub)) {
          MethodSignature sm = view.getIdentifierFactory().getMethodSignature(sub, m.getSubSignature());
          virtualCalls.add(sm);
        }
      });
    }
    return virtualCalls;
  }

  @Nonnull
  @Override
  protected String getAlgorithm() {
    return "RTA";
  }

  @Override
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

  @Override
  protected void populateCallGraph(@Nonnull JavaView view, @Nonnull CallGraph cg) {
    findInstantiatedClasses(view, "exercise2");
    System.out.println("CLASSES: " + this.instantiatedClasses);
    Stream<MethodSignature> methodSignatureStream = getEntryPoints(view);
    methodSignatureStream.forEach(entry -> {
      if (!cg.hasNode(entry)) {
        cg.addNode(entry);
      }
      parseMethodStatements(entry, view, cg);
    });
  }

  protected void findInstantiatedClasses(@Nonnull JavaView view, @Nonnull String packageScope){
    // only scan files under 'exercise2' package.
    Stream<JavaSootClass> allClasses = view.getClasses()
            .stream()
            .filter(clazz -> clazz.getName().contains("." + packageScope + "."));

    // for each class, parse its methods, locate newExprs (exprs with new keyword) and store them.
    allClasses.forEach(clazz -> {
      clazz.getMethods().forEach(method -> {
        if (!method.hasBody())
          return;

        Body body = method.getBody();
        body.getStmts().forEach(stmt -> {
          if (stmt instanceof JAssignStmt){
            JAssignStmt assignStmt = (JAssignStmt) stmt;
            if (assignStmt.getRightOp() instanceof JNewExpr){
              JNewExpr newExpr = (JNewExpr) assignStmt.getRightOp();
              this.instantiatedClasses.add(newExpr.getType());
            }
          }
        });
      });
    });
  }
}
