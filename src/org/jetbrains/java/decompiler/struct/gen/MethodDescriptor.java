// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.struct.gen;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;

public class MethodDescriptor {
  public final VarType[] params;
  public final VarType ret;
  public GenericMethodDescriptor genericInfo;

  private MethodDescriptor(VarType[] params, VarType ret) {
    this.params = params;
    this.ret = ret;
  }

  public static MethodDescriptor parseDescriptor(String descriptor) {
    int parenth = descriptor.lastIndexOf(')');
    if (descriptor.length() < 2 || parenth < 0 || descriptor.charAt(0) != '(') {
      throw new IllegalArgumentException("Invalid descriptor: " + descriptor);
    }

    VarType[] params;

    if (parenth > 1) {
      String parameters = descriptor.substring(1, parenth);
      List<String> lst = new ArrayList<>();

      int indexFrom = -1, ind, len = parameters.length(), index = 0;
      while (index < len) {
        switch (parameters.charAt(index)) {
          case '[':
            if (indexFrom < 0) {
              indexFrom = index;
            }
            break;
          case 'L':
            ind = parameters.indexOf(";", index);
            lst.add(parameters.substring(indexFrom < 0 ? index : indexFrom, ind + 1));
            index = ind;
            indexFrom = -1;
            break;
          default:
            lst.add(parameters.substring(indexFrom < 0 ? index : indexFrom, index + 1));
            indexFrom = -1;
        }
        index++;
      }

      params = new VarType[lst.size()];
      for (int i = 0; i < lst.size(); i++) {
        params[i] = new VarType(lst.get(i));
      }
    }
    else {
      params = VarType.EMPTY_ARRAY;
    }

    VarType ret = new VarType(descriptor.substring(parenth + 1));

    return new MethodDescriptor(params, ret);
  }

  public static MethodDescriptor parseDescriptor(StructMethod struct, ClassNode node) {
    MethodDescriptor md = MethodDescriptor.parseDescriptor(struct.getDescriptor());

    GenericMethodDescriptor sig = struct.getSignature();
    if (sig != null) {
      if (node != null) {
        MethodWrapper methodWrapper = node.getWrapper().getMethodWrapper(struct.getName(), struct.getDescriptor());
        boolean isEnum = struct.getClassStruct().hasModifier(CodeConstants.ACC_ENUM) && DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_ENUM);
        boolean init = CodeConstants.INIT_NAME.equals(struct.getName()) && node.type != ClassNode.CLASS_ANONYMOUS;
        long actualParams = md.params.length;
        List<VarVersionPair> sigFields = methodWrapper == null ? null : methodWrapper.synthParameters;
        if (sigFields != null) {
          actualParams = sigFields.stream().filter(Objects::isNull).count();
        }
        else if (isEnum && init) actualParams -= 2;
        if (actualParams != sig.parameterTypes.size()) {
          String message = "Inconsistent generic signature in method " + struct.getName() + " " + struct.getDescriptor() + " in " + struct.getClassStruct().qualifiedName;
          DecompilerContext.getLogger().writeMessage(message, IFernflowerLogger.Severity.WARN);
          sig = null;
        }
      }
      md.addGenericDescriptor(sig);
    }

    return md;
  }

  public void addGenericDescriptor(GenericMethodDescriptor desc) {
    this.genericInfo = desc;
  }

  public String buildNewDescriptor(NewClassNameBuilder builder) {
    boolean updated = false;

    VarType[] newParams;
    if (params.length > 0) {
      newParams = new VarType[params.length];
      System.arraycopy(params, 0, newParams, 0, params.length);
      for (int i = 0; i < params.length; i++) {
        VarType substitute = buildNewType(params[i], builder);
        if (substitute != null) {
          newParams[i] = substitute;
          updated = true;
        }
      }
    }
    else {
      newParams = VarType.EMPTY_ARRAY;
    }

    VarType newRet = ret;
    VarType substitute = buildNewType(ret, builder);
    if (substitute != null) {
      newRet = substitute;
      updated = true;
    }

    if (updated) {
      StringBuilder res = new StringBuilder("(");
      for (VarType param : newParams) {
        res.append(param);
      }
      res.append(")").append(newRet.toString());
      return res.toString();
    }

    return null;
  }

  private static VarType buildNewType(VarType type, NewClassNameBuilder builder) {
    if (type.type == CodeConstants.TYPE_OBJECT) {
      String newClassName = builder.buildNewClassname(type.value);
      if (newClassName != null) {
        return new VarType(type.type, type.arrayDim, newClassName);
      }
    }
    return null;
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) return true;
    if (!(o instanceof MethodDescriptor)) return false;

    MethodDescriptor md = (MethodDescriptor)o;
    return ret.equals(md.ret) && Arrays.equals(params, md.params);
  }

  @Override
  public int hashCode() {
    int result = ret.hashCode();
    result = 31 * result + params.length;
    return result;
  }
}
