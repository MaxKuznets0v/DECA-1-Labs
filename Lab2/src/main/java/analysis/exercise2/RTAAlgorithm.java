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

  @Nonnull
  @Override
  protected String getAlgorithm() {
    return "RTA";
  }

  @Override
  protected Set<MethodSignature> resolveVirtualCall(ClassType type, MethodSignature m, @Nonnull JavaView view) {
    Set<MethodSignature> virtualCalls = new HashSet<>();
    TypeHierarchy hierarchy = view.getTypeHierarchy();
    if (hierarchy.contains(type)) {
      Stream<ClassType> subtypes = hierarchy.subtypesOf(type);
      subtypes.filter(instantiatedClasses::contains)
              .forEach(sub -> {
                MethodSignature sm = view.getIdentifierFactory().getMethodSignature(sub, m.getSubSignature());
                virtualCalls.add(sm);});
    }
    return virtualCalls;
  }

  @Override
  protected void populateCallGraph(@Nonnull JavaView view, @Nonnull CallGraph cg) {
    /* NOTE: the search for instantiated classes (with new keyword) is done for all files under "exercise2" package
    * This can be changed by setting "packageScope" parameter to the desired package/directory */
    findInstantiatedClasses(view, "exercise2");

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
    Stream<JavaSootClass> allPackageClasses = view.getClasses()
            .stream()
            .filter(clazz -> clazz.getName().contains("." + packageScope + "."));

    // for each class, parse its methods, locate newExprs (exprs with new keyword) and store them.
    allPackageClasses.forEach(clazz -> {
      clazz.getMethods().forEach(method -> {
        if (!method.hasBody())
          return;

        Body body = method.getBody();
        body.getStmts().stream()
                .filter(stmt -> stmt instanceof JAssignStmt)
                .map(stmt -> (JAssignStmt) stmt)
                .map(JAssignStmt::getRightOp)
                .filter(operand -> operand instanceof JNewExpr)
                .map(operand -> (JNewExpr) operand)
                .forEach(newExp -> this.instantiatedClasses.add(newExp.getType()));
      });
    });
  }
}
