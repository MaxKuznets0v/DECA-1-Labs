package analysis.exercise1;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import java.util.*;
import javax.annotation.Nonnull;
import sootup.java.core.views.JavaView;

public class CHAAlgorithm extends CallGraphAlgorithm {

  @Nonnull
  @Override
  protected String getAlgorithm() {
    return "CHA";
  }

  @Override
  protected void populateCallGraph(@Nonnull JavaView view, @Nonnull CallGraph cg) {
    // Your implementation goes here, also feel free to add methods as needed
    // To get your entry points we prepared getEntryPoints(view) in the superclass for you

    // TODO: implement

  }
}
