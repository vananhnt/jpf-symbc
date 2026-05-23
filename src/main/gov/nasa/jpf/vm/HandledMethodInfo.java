/*
 * Compatibility shim: HandledMethodInfo was removed from jpf-core but is
 * still referenced by SkippedMethodInfo / SkippedNativeMethodInfo.
 * Extends NativeMethodInfo with a single-arg (MethodInfo) constructor so
 * the skipping machinery can wrap any method without needing a resolved peer.
 */
package gov.nasa.jpf.vm;

import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.NativeMethodInfo;

public abstract class HandledMethodInfo extends NativeMethodInfo {

  public HandledMethodInfo(MethodInfo mi) {
    super(mi, null, null);
  }

  protected abstract String printInfo();
}
