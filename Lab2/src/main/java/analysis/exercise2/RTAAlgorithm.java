package analysis.exercise2;

import analysis.CallGraph;
import analysis.exercise1.CHAAlgorithm;
import javax.annotation.Nonnull;
import sootup.java.core.views.JavaView;

public class RTAAlgorithm extends CHAAlgorithm {

  @Nonnull
  @Override
  protected String getAlgorithm() {
    return "RTA";
  }

  @Override
  protected void populateCallGraph(@Nonnull JavaView view, @Nonnull CallGraph cg) {
    // Your implementation goes here, also feel free to add methods as needed
    // To get your entry points we prepared getEntryPoints(view) in the superclass for you

    // TODO: implement

  }
}
