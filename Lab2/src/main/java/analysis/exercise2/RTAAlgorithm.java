package analysis.exercise2;

import analysis.exercise1.CHAAlgorithm;
import javax.annotation.Nonnull;
import sootup.core.jimple.common.expr.JNewExpr;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.model.Body;
import sootup.core.signatures.MethodSignature;
import sootup.core.typehierarchy.TypeHierarchy;
import sootup.core.types.ClassType;
import sootup.java.core.views.JavaView;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

public class RTAAlgorithm extends CHAAlgorithm {

  @Nonnull
  @Override
  protected String getAlgorithm() {
    return "RTA";
  }

  @Override
  protected Set<MethodSignature> resolveVirtualCall(ClassType type, MethodSignature m, @Nonnull JavaView view) {
    Set<MethodSignature> virtualCalls = new HashSet<>();
    Set<ClassType> instantiatedClasses = getInstantiatedClasses(view);
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

  protected Set<ClassType> getInstantiatedClasses(@Nonnull JavaView view){
    Set<ClassType> instantiatedClasses = new HashSet<>();

    // for each class, parse its methods, locate newExprs (exprs with new keyword) and store them.
    view.getClasses().forEach(clazz -> {
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
                .forEach(newExp -> instantiatedClasses.add(newExp.getType()));
      });
    });
      return instantiatedClasses;
  }

}
