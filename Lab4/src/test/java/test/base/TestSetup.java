package test.base;

import sootup.core.inputlocation.AnalysisInputLocation;
import sootup.java.bytecode.inputlocation.JavaClassPathAnalysisInputLocation;
import sootup.java.core.JavaSootMethod;
import sootup.java.core.views.JavaView;

import java.io.File;

public abstract class TestSetup {

    protected final JavaView view;

    JavaSootMethod entryPointMethod = null;

    public TestSetup() {

        String classPath = System.getProperty("user.dir") + File.separator + "target" + File.separator + "test-classes";
        AnalysisInputLocation inputLocation = new JavaClassPathAnalysisInputLocation(classPath);
        view = new JavaView(inputLocation);

    }

}
