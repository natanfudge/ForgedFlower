// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.struct.gen.generics;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.InterpreterUtil;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class GenericType extends VarType {

  public static final int WILDCARD_EXTENDS = 1;
  public static final int WILDCARD_SUPER = 2;
  public static final int WILDCARD_UNBOUND = 3;
  public static final int WILDCARD_NO = 4;

  private final VarType parent;
  private final List<VarType> arguments;
  private final int wildcard;

  public static final GenericType DUMMY_VAR = new GenericType(CodeConstants.TYPE_GENVAR, 0, "", null, null, GenericType.WILDCARD_NO);

  public GenericType(int type, int arrayDim, String value, VarType parent, List<VarType> arguments, int wildcard) {
    super(type, arrayDim, value, getFamily(type, arrayDim), getStackSize(type, arrayDim), false);
    this.parent = parent;
    this.arguments = arguments == null ? Collections.<VarType>emptyList() : arguments;
    this.wildcard = wildcard;
  }

  public static VarType parse(String signature) {
    return parse(signature, WILDCARD_NO);
  }

  public static VarType parse(String signature, int wildcard) {
    int type = 0;
    int arrayDim = 0;
    String value = null;
    List<VarType> params = null;
    VarType parent = null;

    int index = 0;
    loop:
    while (index < signature.length()) {
      switch (signature.charAt(index)) {
        case '[':
          arrayDim++;
          break;

        case 'T':
          type = CodeConstants.TYPE_GENVAR;
          value = signature.substring(index + 1, signature.length() - 1);
          break loop;

        case 'L':
          type = CodeConstants.TYPE_OBJECT;
          signature = signature.substring(index + 1, signature.length() - 1);
          String cl = getNextClassSignature(signature);

          if (cl.length() == signature.length()) {
            int argStart = cl.indexOf('<');
            if (argStart >= 0) {
              value = cl.substring(0, argStart);
              params = parseArgumentsList(cl.substring(argStart + 1, cl.length() - 1));
            }
            else {
              value = cl;
            }
          }
          else {
            StringBuilder name_buff = new StringBuilder();
            while (signature.length() > 0) {
              String name = cl;
              String args = null;

              int argStart = cl.indexOf('<');
              if (argStart >= 0) {
                name = cl.substring(0, argStart);
                args = cl.substring(argStart + 1, cl.length() - 1);
              }

              if (name_buff.length() > 0) {
                name_buff.append('$');
              }
              name_buff.append(name);

              value = name_buff.toString();
              params = args == null ? null : parseArgumentsList(args);

              if (cl.length() == signature.length()) {
                break;
              }
              else {
                if (parent == null && params == null) {
                  parent = GenericType.parse("L" + value + ";");
                }
                else {
                  parent = new GenericType(CodeConstants.TYPE_OBJECT, 0, value, parent, params, wildcard);
                }

                signature = signature.substring(cl.length() + 1);
              }
              cl = getNextClassSignature(signature);
            }
          }
          break loop;

        default:
          value = signature.substring(index, index + 1);
          type = VarType.getType(value.charAt(0));
      }

      index++;
    }

    if (type == CodeConstants.TYPE_GENVAR) {
      return new GenericType(type, arrayDim, value, null, null, wildcard);
    }
    else if (type == CodeConstants.TYPE_OBJECT) {
      if (parent == null && params == null && wildcard == WILDCARD_NO) {
        return new VarType(type, arrayDim, value);
      }
      else {
        return new GenericType(type, arrayDim, value, parent, params, wildcard);
      }
    }
    else {
      return new VarType(type, arrayDim, value);
    }
  }

  private static String getNextClassSignature(String value) {
    int counter = 0;
    int index = 0;

    loop:
    while (index < value.length()) {
      switch (value.charAt(index)) {
        case '<':
          counter++;
          break;
        case '>':
          counter--;
          break;
        case '.':
          if (counter == 0) {
            break loop;
          }
      }

      index++;
    }

    return value.substring(0, index);
  }

  private static List<VarType> parseArgumentsList(String value) {
    if (value == null) {
      return null;
    }

    List<VarType> args = new ArrayList<VarType>();

    while (value.length() > 0) {
      String typeStr = getNextType(value);
      int len = typeStr.length();
      int wildcard = WILDCARD_NO;

      switch (typeStr.charAt(0)) {
        case '*':
          wildcard = WILDCARD_UNBOUND;
          break;
        case '+':
          wildcard = WILDCARD_EXTENDS;
          break;
        case '-':
          wildcard = WILDCARD_SUPER;
          break;
      }

      if (wildcard != WILDCARD_NO) {
        typeStr = typeStr.substring(1);
      }

      args.add(typeStr.length() == 0 ? null : GenericType.parse(typeStr, wildcard));

      value = value.substring(len);
    }

    return args;
  }

  public static String getNextType(String value) {
    int counter = 0;
    int index = 0;

    boolean contMode = false;

    loop:
    while (index < value.length()) {
      switch (value.charAt(index)) {
        case '*':
          if (!contMode) {
            break loop;
          }
          break;
        case 'L':
        case 'T':
          if (!contMode) {
            contMode = true;
          }
        case '[':
        case '+':
        case '-':
          break;
        default:
          if (!contMode) {
            break loop;
          }
          break;
        case '<':
          counter++;
          break;
        case '>':
          counter--;
          break;
        case ';':
          if (counter == 0) {
            break loop;
          }
      }

      index++;
    }

    return value.substring(0, index + 1);
  }

  public GenericType decreaseArrayDim() {
    assert arrayDim > 0 : this;
    return new GenericType(type, arrayDim - 1, value, parent, arguments, wildcard);
  }

  public VarType resizeArrayDim(int newArrayDim) {
    return new GenericType(type, newArrayDim, value, parent, arguments, wildcard);
  }

  public VarType getParent() {
    return parent;
  }

  public List<VarType> getArguments() {
    return arguments;
  }
  @Override
  public boolean isGeneric() {
    return type == CodeConstants.TYPE_GENVAR || !arguments.isEmpty() || parent != null || wildcard != WILDCARD_NO;
  }

  public int getWildcard() {
    return wildcard;
  }

  public String getCastName() {
    String clsName = null;
    if (parent == null) {
      clsName = DecompilerContext.getImportCollector().getShortName(value.replace('/', '.'));
    }
    else if (parent.isGeneric()) {
      clsName = ((GenericType)parent).getCastName() + "." + value.substring(parent.value.length() + 1);
    }
    else {
      clsName = DecompilerContext.getImportCollector().getShortName(parent.value.replace('/', '.')) + "." + value.substring(value.lastIndexOf('.') + 1);
    }
    return clsName + getTypeArguments();
  }

  private String getTypeArguments() {
    StringBuilder buffer = new StringBuilder();
    if (!arguments.isEmpty()) {
      buffer.append('<');

      for (int i = 0; i < arguments.size(); i++) {
        if (i > 0) {
          buffer.append(", ");
        }

        VarType par = arguments.get(i);
        if (par == null) { // Wildcard unbound
          buffer.append('?');
        }
        else if (par.isGeneric()) {
          GenericType gen = (GenericType)par;
          switch (gen.getWildcard()) {
            case GenericType.WILDCARD_EXTENDS:
              buffer.append("? extends ");
              break;
            case GenericType.WILDCARD_SUPER:
              buffer.append("? super ");
              break;
          }
          buffer.append(GenericMain.getGenericCastTypeName(gen));
        }
        else {
          buffer.append(ExprProcessor.getCastTypeName(par));
        }
      }

      buffer.append(">");
    }
    return buffer.toString();
  }

  @Override
  public String toString() {
    StringBuilder buf = new StringBuilder();
    switch(getWildcard()) {
      case GenericType.WILDCARD_EXTENDS:
        buf.append("? extends ");
        break;
      case GenericType.WILDCARD_SUPER:
        buf.append("? super ");
      break;
    }
    buf.append(super.toString());
    buf.append(getTypeArguments());
    return buf.toString();
  }


  @Override
  public VarType remap(Map<VarType, VarType> map) {
    VarType main = super.remap(map);
    if (main != this) {
      return main;
    }
    boolean changed = false;
    VarType parent = getParent();
    if (map.containsKey(parent)) {
      parent = map.get(parent);
      changed = true;
    }
    List<VarType> newArgs = new ArrayList<VarType>();
    for (VarType arg : getArguments()) {
      VarType newArg = null;
      if (arg != null) {
        newArg = arg.remap(map);
      }
      if (newArg != arg) {
        newArgs.add(newArg);
        changed = true;
      } else {
        newArgs.add(arg);
      }
    }
    if (changed) {
      return new GenericType(main.type, main.arrayDim, main.value, parent, newArgs, getWildcard());
    }
    return this;
  }

  public boolean equalsExact(Object o) {
    if (o == this) {
      return true;
    }

    if (!(o instanceof VarType)) {
      return false;
    }

    if (!(o instanceof GenericType)) {
      return parent == null && arguments.isEmpty() && wildcard == WILDCARD_NO && o.equals(this);
    }

    GenericType gt = (GenericType)o;
    if (type != gt.type || arrayDim != gt.arrayDim || wildcard != gt.wildcard || !InterpreterUtil.equalObjects(value, gt.value)) {
      return false;
    }

    return this.argumentsEqual(gt);
  }

  public boolean argumentsEqual(GenericType gt) {
    if (arguments.size() != gt.arguments.size()) {
      return false;
    }

    for (int i = 0; i < arguments.size(); ++i) {
      VarType t = arguments.get(i);
      VarType o = gt.arguments.get(i);

      if (t == null && o == null) {
        continue;
      }

      if (t == null || o == null || t.isGeneric() != o.isGeneric() || !t.equals(o)) {
        return false;
      }

      if ((t.isGeneric() && !((GenericType)t).equalsExact(o))) {
        return false;
      }
    }
    return true;
  }

  public List<GenericType> getAllGenericVars() {
    List<GenericType> ret = new ArrayList<>();

    if (this.type == CodeConstants.TYPE_GENVAR) {
      ret.add((GenericType)this.resizeArrayDim(0));
      return ret;
    }

    for (VarType arg : arguments) {
      if (arg != null && arg.isGeneric()) {
        ret.addAll(((GenericType)arg).getAllGenericVars());
      }
    }
    return ret;
  }

  public void mapGenVarsTo(GenericType other, Map<VarType, VarType> map) {
    if (arguments.size() == other.arguments.size()) {
      for (int i = 0; i < arguments.size(); ++i) {
        VarType thisArg = arguments.get(i);
        VarType otherArg = other.arguments.get(i);

        if (thisArg != null) {
          if (thisArg.type == CodeConstants.TYPE_GENVAR) {
            if (otherArg == null && thisArg.arrayDim == 0) {
              if (!map.containsKey(thisArg)) {
                map.put(thisArg, otherArg);
              }
            }
            else if (otherArg != null && thisArg.arrayDim <= otherArg.arrayDim) {
              if (thisArg.arrayDim > 0) {
                otherArg = otherArg.resizeArrayDim(otherArg.arrayDim - thisArg.arrayDim);
                thisArg = thisArg.resizeArrayDim(0);
              }
              if (!map.containsKey(thisArg)) {
                map.put(thisArg, otherArg);
              }
            }
          }
          else if (thisArg.isGeneric() && otherArg != null && otherArg.isGeneric()) {
            ((GenericType)thisArg).mapGenVarsTo((GenericType)otherArg, map);
          }
        }
      }
    }
  }

  public boolean hasUnknownGenericType(Set<VarType> namedGenerics) {
    if (type == CodeConstants.TYPE_GENVAR) {
      return !namedGenerics.contains(this.resizeArrayDim(0));
    }

    for (VarType arg : arguments) {
      if (arg != null && arg.isGeneric() && ((GenericType)arg).hasUnknownGenericType(namedGenerics)) {
        return true;
      }
    }
    return false;
  }

  public static VarType getGenericSuperType(VarType derivedType, VarType superType) {
    StructClass dcls = DecompilerContext.getStructContext().getClass(derivedType.value);
    StructClass scls = DecompilerContext.getStructContext().getClass(superType.value);

    if (dcls != null && scls != null) {
      Map<String, Map<VarType, VarType>> hierarchy = dcls.getAllGenerics();

      if (hierarchy.containsKey(scls.qualifiedName) && scls.getSignature() != null) {
        Map<VarType, VarType> tempMap = new HashMap<>();

        if (derivedType.isGeneric() && dcls.getSignature() != null) {
          dcls.getSignature().genericType.mapGenVarsTo((GenericType)derivedType, tempMap);
        }
        return scls.getSignature().genericType.remap(hierarchy.get(scls.qualifiedName)).remap(tempMap);
      }
    }
    return derivedType;
  }
}
