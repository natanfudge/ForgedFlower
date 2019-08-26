/*
 * Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
 */
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.main.collectors.BytecodeMappingTracer;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.ClasspathHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.CheckTypesResult;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.struct.match.MatchEngine;
import org.jetbrains.java.decompiler.struct.match.MatchNode;
import org.jetbrains.java.decompiler.struct.match.MatchNode.RuleValue;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.ListStack;
import org.jetbrains.java.decompiler.util.TextUtil;

import java.lang.reflect.Method;
import java.util.*;
import java.util.Map.Entry;

public class InvocationExprent extends Exprent {

  public static final int INVOKE_SPECIAL = 1;
  public static final int INVOKE_VIRTUAL = 2;
  public static final int INVOKE_STATIC = 3;
  public static final int INVOKE_INTERFACE = 4;
  public static final int INVOKE_DYNAMIC = 5;

  public static final int TYP_GENERAL = 1;
  public static final int TYP_INIT = 2;
  public static final int TYP_CLINIT = 3;

  private static final BitSet EMPTY_BIT_SET = new BitSet(0);

  private String name;
  private String classname;
  private boolean isStatic;
  private boolean canIgnoreBoxing = true;
  private int functype = TYP_GENERAL;
  private Exprent instance;
  private StructMethod desc = null;
  private MethodDescriptor descriptor;
  private String stringDescriptor;
  private String invokeDynamicClassSuffix;
  private int invocationTyp = INVOKE_VIRTUAL;
  private List<Exprent> lstParameters = new ArrayList<>();
  private List<PooledConstant> bootstrapArguments;
  private List<VarType> genericArgs = new ArrayList<>();
  private Map<VarType, VarType> genericsMap = new HashMap<>();
  private boolean isInvocationInstance = false;
  private boolean forceBoxing = false;
  private boolean isSyntheticGetClass = false;

  public InvocationExprent() {
    super(EXPRENT_INVOCATION);
  }

  public InvocationExprent(int opcode,
                           LinkConstant cn,
                           List<PooledConstant> bootstrapArguments,
                           ListStack<Exprent> stack,
                           BitSet bytecodeOffsets) {
    this();

    name = cn.elementname;
    classname = cn.classname;
    this.bootstrapArguments = bootstrapArguments;
    switch (opcode) {
      case CodeConstants.opc_invokestatic:
        invocationTyp = INVOKE_STATIC;
        break;
      case CodeConstants.opc_invokespecial:
        invocationTyp = INVOKE_SPECIAL;
        break;
      case CodeConstants.opc_invokevirtual:
        invocationTyp = INVOKE_VIRTUAL;
        break;
      case CodeConstants.opc_invokeinterface:
        invocationTyp = INVOKE_INTERFACE;
        break;
      case CodeConstants.opc_invokedynamic:
        invocationTyp = INVOKE_DYNAMIC;

        classname = "java/lang/Class"; // dummy class name
        invokeDynamicClassSuffix = "##Lambda_" + cn.index1 + "_" + cn.index2;
    }

    if (CodeConstants.INIT_NAME.equals(name)) {
      functype = TYP_INIT;
    }
    else if (CodeConstants.CLINIT_NAME.equals(name)) {
      functype = TYP_CLINIT;
    }

    stringDescriptor = cn.descriptor;
    descriptor = MethodDescriptor.parseDescriptor(cn.descriptor);

    for (VarType ignored : descriptor.params) {
      lstParameters.add(0, stack.pop());
    }

    if (opcode == CodeConstants.opc_invokedynamic) {
      int dynamicInvocationType = -1;
      if (bootstrapArguments != null) {
        if (bootstrapArguments.size() > 1) { // INVOKEDYNAMIC is used not only for lambdas
          PooledConstant link = bootstrapArguments.get(1);
          if (link instanceof LinkConstant) {
            dynamicInvocationType = ((LinkConstant)link).index1;
          }
        }
      }
      if (dynamicInvocationType == CodeConstants.CONSTANT_MethodHandle_REF_invokeStatic) {
        isStatic = true;
      }
      else {
        // FIXME: remove the first parameter completely from the list. It's the object type for a virtual lambda method.
        if (!lstParameters.isEmpty()) {
          instance = lstParameters.get(0);
        }
      }
    }
    else if (opcode == CodeConstants.opc_invokestatic) {
      isStatic = true;
    }
    else {
      instance = stack.pop();
    }

    addBytecodeOffsets(bytecodeOffsets);
  }

  private InvocationExprent(InvocationExprent expr) {
    this();

    name = expr.getName();
    classname = expr.getClassname();
    isStatic = expr.isStatic();
    canIgnoreBoxing = expr.canIgnoreBoxing;
    functype = expr.getFunctype();
    instance = expr.getInstance();
    if (instance != null) {
      instance = instance.copy();
    }
    invocationTyp = expr.getInvocationTyp();
    invokeDynamicClassSuffix = expr.getInvokeDynamicClassSuffix();
    stringDescriptor = expr.getStringDescriptor();
    descriptor = expr.getDescriptor();
    lstParameters = new ArrayList<>(expr.getLstParameters());
    ExprProcessor.copyEntries(lstParameters);

    addBytecodeOffsets(expr.bytecode);
    bootstrapArguments = expr.getBootstrapArguments();
    isSyntheticGetClass = expr.isSyntheticGetClass();

    if (invocationTyp == INVOKE_DYNAMIC && !isStatic && instance != null && !lstParameters.isEmpty()) {
      // method reference, instance and first param are expected to be the same var object
      instance = lstParameters.get(0);
    }
  }

  @Override
  public VarType getExprType() {
    return descriptor.ret;
  }


  @Override
  public VarType getInferredExprType(VarType upperBound) {
    if (desc == null) {
      StructClass cl = DecompilerContext.getStructContext().getClass(classname);
      desc = cl != null ? cl.getMethodRecursive(name, stringDescriptor) : null;
    }

    genericArgs.clear();
    genericsMap.clear();

    StructClass mthCls = DecompilerContext.getStructContext().getClass(classname);

    if (desc != null && mthCls != null) {
      boolean isNew = functype == TYP_INIT && mthCls.getSignature() != null;
      if (desc.getSignature() != null || isNew) {
        Map<VarType, List<VarType>> named = getNamedGenerics();
        Map<VarType, List<VarType>> bounds = getGenericBounds(mthCls);

        List<String> fparams = isNew ? mthCls.getSignature().fparameters : desc.getSignature().typeParameters;
        VarType ret = isNew ? mthCls.getSignature().genericType : desc.getSignature().returnType;

        StructClass cls;
        Map<VarType, VarType> tempMap = new HashMap<>();

        if (instance != null && !isNew) {
          instance.setInvocationInstance();

          VarType instType;

          // don't want the casted type
          if (instance.type == EXPRENT_FUNCTION && ((FunctionExprent)instance).getFuncType() == FunctionExprent.FUNCTION_CAST) {
            instType = ((FunctionExprent)instance).getLstOperands().get(0).getInferredExprType(upperBound);
          }
          else {
            instType = instance.getInferredExprType(upperBound);
          }

          if (instType.isGeneric() && instType.type != CodeConstants.TYPE_GENVAR) {
            GenericType ginstance = (GenericType)instType;

            cls = DecompilerContext.getStructContext().getClass(instType.value);
            if (cls != null && cls.getSignature() != null) {
              cls.getSignature().genericType.mapGenVarsTo(ginstance, tempMap);
              tempMap.forEach((from, to) -> processGenericMapping(from, to, named, bounds));
              tempMap.clear();
            }
          }
        }

        if (!classname.equals(desc.getClassStruct().qualifiedName)) {
          Map<String, Map<VarType, VarType>> hierarchy = mthCls.getAllGenerics();
          if (hierarchy.containsKey(desc.getClassStruct().qualifiedName)) {
            hierarchy.get(desc.getClassStruct().qualifiedName).forEach((from, to) -> {
              if (!genericsMap.containsKey(from) && !to.equals(from)) {
                if (to.type == CodeConstants.TYPE_GENVAR) {
                  if (genericsMap.containsKey(to)) {
                    genericsMap.put(from, to.remap(genericsMap));
                  }
                }
                else if (!bounds.containsKey(from)) {
                  genericsMap.put(from, to);
                }
              }
            });
          }
        }

        // fix for this() & super()
        if (upperBound == null && isNew) {
          ClassNode currentCls = (ClassNode)DecompilerContext.getProperty(DecompilerContext.CURRENT_CLASS_NODE);

          if (mthCls.equals(currentCls.classStruct)) {
            mthCls.getSignature().genericType.getAllGenericVars().forEach(var -> genericsMap.put(var, var));
          }
          else {
            Map<String, Map<VarType, VarType>> hierarchy = currentCls.classStruct.getAllGenerics();
            if (hierarchy.containsKey(mthCls.qualifiedName)) {
              hierarchy.get(mthCls.qualifiedName).forEach(genericsMap::put);
            }
          }
        }

        Map<VarType, VarType> upperBoundsMap = new HashMap<>();
        if (upperBound != null && !upperBound.equals(VarType.VARTYPE_OBJECT) && (upperBound.type != CodeConstants.TYPE_GENVAR || named.containsKey(upperBound))) {
          VarType ub = upperBound; // keep original
          if (ub.type != CodeConstants.TYPE_GENVAR && ret.type != CodeConstants.TYPE_GENVAR && !ub.value.equals(ret.value)) {
            if (DecompilerContext.getStructContext().instanceOf(ub.value, ret.value)) {
              ub = GenericType.getGenericSuperType(ub, ret);
            }
            else {
              ret = GenericType.getGenericSuperType(ret, ub);
            }
          }

          if (ret.type == CodeConstants.TYPE_GENVAR) {
            upperBoundsMap.put(ret.resizeArrayDim(0), upperBound.resizeArrayDim(upperBound.arrayDim - ret.arrayDim));
          }
          else {
            gatherGenerics(ub, ret, tempMap);
            tempMap.forEach((from, to) -> {
              if (!genericsMap.containsKey(from)) {
                if (to != null && (to.type != CodeConstants.TYPE_GENVAR || named.containsKey(to))) {
                  if (isMappingInBounds(from, to, named, bounds)) {
                    if (!isInvocationInstance) {
                      genericsMap.put(from, to);
                    }
                    upperBoundsMap.put(from, to);
                  }
                }
              }
            });
            tempMap.clear();
          }
        }

        Set<VarType> paramGenerics = new HashSet<>();
        if (!lstParameters.isEmpty() && desc.getSignature() != null) {
          List<VarVersionPair> mask = null;
          int start = 0;
          if (isNew) {
            ClassNode newNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(classname);
            if (newNode != null) {
              mask = ExprUtil.getSyntheticParametersMask(newNode, stringDescriptor, lstParameters.size());
              start = newNode.classStruct.hasModifier(CodeConstants.ACC_ENUM) ? 2 : 0;
            }
          }

          int j = 0;
          for (int i = start; i < lstParameters.size(); ++i) {
            if (mask == null || mask.get(i) != null) {
              VarType paramType = desc.getSignature().parameterTypes.get(j++);
              if (paramType.isGeneric()) {

                VarType paramUB = paramType.remap(genericsMap);
                if (paramUB == paramType) {
                  paramUB = paramType.remap(upperBoundsMap);
                }

                VarType argtype;
                if (lstParameters.get(i).type == EXPRENT_FUNCTION && ((FunctionExprent)lstParameters.get(i)).getFuncType() == FunctionExprent.FUNCTION_CAST) {
                  argtype = ((FunctionExprent)lstParameters.get(i)).getLstOperands().get(0).getInferredExprType(paramUB);
                }
                else {
                  argtype = lstParameters.get(i).getInferredExprType(paramUB);
                }

                StructClass paramCls = DecompilerContext.getStructContext().getClass(paramType.value);
                cls = argtype.type != CodeConstants.TYPE_GENVAR ? DecompilerContext.getStructContext().getClass(argtype.value) : null;

                if (cls != null && paramCls != null) {
                  if (paramType.isGeneric() && !paramType.value.equals(argtype.value)) {
                    argtype = GenericType.getGenericSuperType(argtype, paramType);
                  }

                  if (paramType.isGeneric() && argtype.isGeneric()) {
                    GenericType genParamType = (GenericType)paramType;
                    GenericType genArgType = (GenericType)argtype;

                    genParamType.mapGenVarsTo(genArgType, tempMap);
                    tempMap.forEach((from, to) -> {
                      paramGenerics.add(from);
                      processGenericMapping(from, to, named, bounds);
                    });
                    tempMap.clear();
                  }
                }
                else if (paramType.type == CodeConstants.TYPE_GENVAR && !paramType.equals(argtype) && argtype.arrayDim >= paramType.arrayDim) {
                  if (paramType.arrayDim > 0) {
                    argtype = argtype.resizeArrayDim(argtype.arrayDim - paramType.arrayDim);
                    paramType = paramType.resizeArrayDim(0);
                  }
                  paramGenerics.add(paramType);
                  processGenericMapping(paramType, argtype, named, bounds);
                }
              }
            }
          }
        }

        if (instance != null && mthCls.getSignature() != null) {
          mthCls.getSignature().genericType.getAllGenericVars().forEach(upperBoundsMap::remove);
        }
        upperBoundsMap.forEach(genericsMap::putIfAbsent);

        if (!genericsMap.isEmpty()) {
          VarType newRet = ret;

          if (!mthCls.qualifiedName.equals(desc.getClassStruct().qualifiedName)) {
            Map<String, Map<VarType, VarType>> hierarchy = mthCls.getAllGenerics();
            if (hierarchy.containsKey(desc.getClassStruct().qualifiedName)) {
              newRet = ret.remap(hierarchy.get(desc.getClassStruct().qualifiedName));
            }
          }

          boolean skipArgs = true;
          if (!fparams.isEmpty() && newRet.isGeneric()) {
            for (VarType genVar : ((GenericType)newRet).getAllGenericVars()) {
              if (fparams.contains(genVar.value)) {
                skipArgs = false;
                break;
              }
            }
          }

          newRet = newRet.remap(genericsMap);
          if (newRet == null) {
            newRet = bounds.get(ret).get(0);
          }

          if (!skipArgs) {
            boolean missing = paramGenerics.isEmpty();

            if (!missing) {
              for (String param : fparams) {
                if (!paramGenerics.contains(GenericType.parse("T" + param + ";"))) {
                  missing = true;
                  break;
                }
              }
            }

            boolean suppress = (!missing || !isInvocationInstance) &&
              (upperBound == null || !newRet.isGeneric() || DecompilerContext.getStructContext().instanceOf(newRet.value, upperBound.value));

            if (!suppress) {
              getGenericArgs(fparams, genericsMap, genericArgs);
            }
            else if (isNew) {
              genericArgs.add(GenericType.DUMMY_VAR);
            }
          }

          if (newRet != ret && !(newRet.isGeneric() && ((GenericType)newRet).hasUnknownGenericType(named.keySet()))) {
            return newRet;
          }
        }

        if (ret.isGeneric() && ((GenericType)ret).getAllGenericVars().isEmpty()) {
          return ret;
        }
      }
    }

    return getExprType();
  }


  @Override
  public CheckTypesResult checkExprTypeBounds() {
    CheckTypesResult result = new CheckTypesResult();

    for (int i = 0; i < lstParameters.size(); i++) {
      Exprent parameter = lstParameters.get(i);

      VarType leftType = descriptor.params[i];

      result.addMinTypeExprent(parameter, VarType.getMinTypeInFamily(leftType.typeFamily));
      result.addMaxTypeExprent(parameter, leftType);
    }

    return result;
  }

  @Override
  public List<Exprent> getAllExprents() {
    List<Exprent> lst = new ArrayList<>();
    if (instance != null) {
      lst.add(instance);
    }
    lst.addAll(lstParameters);
    return lst;
  }


  @Override
  public Exprent copy() {
    return new InvocationExprent(this);
  }

  @Override
  public TextBuffer toJava(int indent, BytecodeMappingTracer tracer) {
    TextBuffer buf = new TextBuffer();

    String super_qualifier = null;
    boolean isInstanceThis = false;

    tracer.addMapping(bytecode);

    if (instance instanceof InvocationExprent) {
      ((InvocationExprent) instance).markUsingBoxingResult();
    }

    if (isStatic) {
      if (isBoxingCall() && canIgnoreBoxing && !forceBoxing) {
        // process general "boxing" calls, e.g. 'Object[] data = { true }' or 'Byte b = 123'
        // here 'byte' and 'short' values do not need an explicit narrowing type cast
        ExprProcessor.getCastedExprent(lstParameters.get(0), descriptor.params[0], buf, indent, false, false, false, tracer);
        return buf;
      }

      ClassNode node = (ClassNode)DecompilerContext.getProperty(DecompilerContext.CURRENT_CLASS_NODE);
      if (node == null || !classname.equals(node.classStruct.qualifiedName)) {
        buf.append(DecompilerContext.getImportCollector().getShortNameInClassContext(ExprProcessor.buildJavaClassName(classname)));
      }
    }
    else {

      if (instance != null && instance.type == Exprent.EXPRENT_VAR) {
        VarExprent instVar = (VarExprent)instance;
        VarVersionPair varPair = new VarVersionPair(instVar);

        VarProcessor varProc = instVar.getProcessor();
        if (varProc == null) {
          MethodWrapper currentMethod = (MethodWrapper)DecompilerContext.getProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
          if (currentMethod != null) {
            varProc = currentMethod.varproc;
          }
        }

        String this_classname = null;
        if (varProc != null) {
          this_classname = varProc.getThisVars().get(varPair);
        }

        if (this_classname != null) {
          isInstanceThis = true;

          if (invocationTyp == INVOKE_SPECIAL) {
            if (!classname.equals(this_classname)) { // TODO: direct comparison to the super class?
              StructClass cl = DecompilerContext.getStructContext().getClass(classname);
              boolean isInterface = cl != null && cl.hasModifier(CodeConstants.ACC_INTERFACE);
              super_qualifier = !isInterface ? this_classname : classname;
            }
          }
        }
      }

      if (functype == TYP_GENERAL) {
        if (super_qualifier != null) {
          TextUtil.writeQualifiedSuper(buf, super_qualifier);
        }
        else if (instance != null) {
          StructClass cl = DecompilerContext.getStructContext().getClass(classname);

          VarType leftType = new VarType(CodeConstants.TYPE_OBJECT, 0, classname);
          if (!genericsMap.isEmpty() && cl != null && cl.getSignature() != null) {
            VarType _new = cl.getSignature().genericType.remap(genericsMap);
            if (_new != cl.getSignature().genericType) {
              leftType = _new;
            }
          }

          instance.setInvocationInstance();
          VarType rightType = instance.getInferredExprType(leftType);

          if (isUnboxingCall()) {
            // we don't print the unboxing call - no need to bother with the instance wrapping / casting
            if (instance.type == Exprent.EXPRENT_FUNCTION) {
              FunctionExprent func = (FunctionExprent)instance;
              if (func.getFuncType() == FunctionExprent.FUNCTION_CAST && func.getLstOperands().get(1).type == Exprent.EXPRENT_CONST) {
                ConstExprent _const = (ConstExprent)func.getLstOperands().get(1);
                if (this.classname.equals(_const.getConstType().value)) {
                    buf.append(func.getLstOperands().get(0).toJava(indent, tracer));
                    return buf;
                }
              }
            }
            buf.append(instance.toJava(indent, tracer));
            return buf;
          }

          TextBuffer res = instance.toJava(indent, tracer);

          boolean skippedCast = instance.type == EXPRENT_FUNCTION &&
            ((FunctionExprent)instance).getFuncType() == FunctionExprent.FUNCTION_CAST && !((FunctionExprent)instance).doesCast();

          if (rightType.equals(VarType.VARTYPE_OBJECT) && !leftType.equals(rightType)) {
            buf.append("((").append(ExprProcessor.getCastTypeName(leftType)).append(")");

            if (instance.getPrecedence() >= FunctionExprent.getPrecedence(FunctionExprent.FUNCTION_CAST)) {
              res.enclose("(", ")");
            }
            buf.append(res).append(")");
          }
          else if (instance.getPrecedence() > getPrecedence() && !skippedCast) {
            buf.append("(").append(res).append(")");
          }
          else {
            buf.append(res);
          }
        }
      }
    }

    switch (functype) {
      case TYP_GENERAL:
        if (VarExprent.VAR_NAMELESS_ENCLOSURE.equals(buf.toString())) {
          buf = new TextBuffer();
        }

        if (buf.length() > 0) {
          buf.append(".");
          this.appendParameters(buf, genericArgs);
        }

        buf.append(name);
        if (invocationTyp == INVOKE_DYNAMIC) {
          buf.append("<invokedynamic>");
        }
        buf.append("(");
        break;

      case TYP_CLINIT:
        throw new RuntimeException("Explicit invocation of " + CodeConstants.CLINIT_NAME);

      case TYP_INIT:
        if (super_qualifier != null) {
          buf.append("super(");
        }
        else if (isInstanceThis) {
          buf.append("this(");
        }
        else if (instance != null) {
          buf.append(instance.toJava(indent, tracer)).append(".<init>(");
        }
        else {
          throw new RuntimeException("Unrecognized invocation of " + CodeConstants.INIT_NAME);
        }
    }

    buf.append(appendParamList(indent, tracer)).append(')');
    return buf;
  }

  public TextBuffer appendParamList(int indent, BytecodeMappingTracer tracer) {
    TextBuffer buf = new TextBuffer();
    List<VarVersionPair> mask = null;
    boolean isEnum = false;
    if (functype == TYP_INIT) {
      ClassNode newNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(classname);
      if (newNode != null) {
        mask = ExprUtil.getSyntheticParametersMask(newNode, stringDescriptor, lstParameters.size());
        isEnum = newNode.classStruct.hasModifier(CodeConstants.ACC_ENUM) && DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_ENUM);
      }
    }
    StructClass currCls = ((ClassNode)DecompilerContext.getProperty(DecompilerContext.CURRENT_CLASS_NODE)).classStruct;
    List<StructMethod> matches = getMatchedDescriptors();
    BitSet setAmbiguousParameters = getAmbiguousParameters(matches);

    // omit 'new Type[] {}' for the last parameter of a vararg method call
    if (lstParameters.size() == descriptor.params.length && isVarArgCall()) {
      Exprent lastParam = lstParameters.get(lstParameters.size() - 1);
      if (lastParam.type == EXPRENT_NEW && lastParam.getExprType().arrayDim >= 1) {
        ((NewExprent) lastParam).setVarArgParam(true);
      }
    }

    int start = isEnum ? 2 : 0;
    List<Exprent> parameters = new ArrayList<>(lstParameters);
    VarType[] types = Arrays.copyOf(descriptor.params, descriptor.params.length);
    for (int i = start; i < parameters.size(); i++) {
      Exprent par = parameters.get(i);

      // "unbox" invocation parameters, e.g. 'byteSet.add((byte)123)' or 'new ShortContainer((short)813)'
      //However, we must make sure we don't accidentally make the call ambiguous.
      //An example being List<Integer>, remove(Integer.valueOf(1)) and remove(1) are different functions
      if (par.type == Exprent.EXPRENT_INVOCATION && ((InvocationExprent)par).isBoxingCall()) {
        InvocationExprent inv = (InvocationExprent)par;
        Exprent value = inv.lstParameters.get(0);
        types[i] = value.getExprType(); //Infer?
        //Unboxing in this case is lossy, so we need to explicitly set the type
        if (types[i] .typeFamily == CodeConstants.TYPE_FAMILY_INTEGER) {
          types[i] =
              "java/lang/Short".equals(inv.classname) ? VarType.VARTYPE_SHORT :
              "java/lang/Byte".equals(inv.classname) ? VarType.VARTYPE_BYTE :
              "java/lang/Integer".equals(inv.classname) ? VarType.VARTYPE_INT :
               VarType.VARTYPE_CHAR;
        }

        int count = 0;
        StructClass stClass = DecompilerContext.getStructContext().getClass(classname);
        if (stClass != null) {
          nextMethod:
          for (StructMethod mt : stClass.getMethods()) {
            if (name.equals(mt.getName()) && canAccess(currCls, mt)) {
              MethodDescriptor md = MethodDescriptor.parseDescriptor(mt.getDescriptor());
              if (md.params.length == descriptor.params.length) {
                for (int x = 0; x < md.params.length; x++) {
                  if (md.params[x].typeFamily != descriptor.params[x].typeFamily &&
                      md.params[x].typeFamily != types[x].typeFamily) {
                    continue nextMethod;
                  }
                }
                count++;
              }
            }
          }
        }

        if (count != matches.size()) { //We become more ambiguous? Lets keep the explicit boxing
          types[i] = descriptor.params[i];
          inv.forceBoxing = true;
        }
        else {
          value.addBytecodeOffsets(inv.bytecode); //Keep the bytecode for matching/debug
          parameters.set(i, value);
        }
      }

    }

    if (desc == null) {
      StructClass cl = DecompilerContext.getStructContext().getClass(classname);
      desc = cl != null ? cl.getMethodRecursive(name, stringDescriptor) : null;

      if (instance != null && functype != TYP_INIT) {
        VarType instType = instance.getInferredExprType(null);
        if (instType.isGeneric() && instType.type != CodeConstants.TYPE_GENVAR) {
          GenericType ginstance = (GenericType)instType;

          StructClass cls = DecompilerContext.getStructContext().getClass(instType.value);
          if (cls != null && cls.getSignature() != null) {
            cls.getSignature().genericType.mapGenVarsTo(ginstance, genericsMap);
          }
        }
      }
    }
    if (desc != null && desc.getSignature() != null) {
      Set<VarType> namedGens = getNamedGenerics().keySet();
      int y = 0;
      for (int x = start; x < types.length; x++) {
        if (mask == null || mask.get(x) == null) {
          VarType type = desc.getSignature().parameterTypes.get(y++).remap(genericsMap);
          if (type != null && !(type.isGeneric() && ((GenericType)type).hasUnknownGenericType(namedGens))) {
            types[x] = type;
          }
        }
      }
    }


    boolean firstParameter = true;
    for (int i = start; i < lstParameters.size(); i++) {
      if (mask == null || mask.get(i) == null) {
        TextBuffer buff = new TextBuffer();
        boolean ambiguous = setAmbiguousParameters.get(i);
        /*
        VarType type = descriptor.params[i];

        // using info from the generic signature
        if (desc != null && desc.getSignature() != null && desc.getSignature().params.size() == lstParameters.size()) {
          type = desc.getSignature().params.get(i);
        }

        // applying generic info from the signature
        VarType remappedType = type.remap(genArgs);
        if(type != remappedType) {
          type = remappedType;
        }
        else if (desc != null && desc.getSignature() != null && genericArgs.size() != 0) { // and from the inferred generic arguments
          Map<VarType, VarType> genMap = new HashMap<VarType, VarType>();
          for (int j = 0; j < genericArgs.size(); j++) {
            VarType from = GenericType.parse("T" + desc.getSignature().fparameters.get(j) + ";");
            VarType to = genericArgs.get(j);
            genMap.put(from, to);
          }
        }

        // not passing it along if what we get back is more specific
        VarType exprType = lstParameters.get(i).getInferredExprType(type);
        if (exprType != null && type != null && type.type == CodeConstants.TYPE_GENVAR) {
          //type = exprType;
        }
        */

        Exprent param = unboxIfNeeded(lstParameters.get(i));

        if (i == parameters.size() - 1 && param.getExprType() == VarType.VARTYPE_NULL && NewExprent.probablySyntheticParameter(descriptor.params[i].value)) {
          break;  // skip last parameter of synthetic constructor call
        }

        // 'byte' and 'short' literals need an explicit narrowing type cast when used as a parameter
        ExprProcessor.getCastedExprent(param, types[i], buff, indent, true, ambiguous, true, tracer);

        // the last "new Object[0]" in the vararg call is not printed
        if (buff.length() > 0) {
          if (!firstParameter) {
            buf.append(", ");
          }
          buf.append(buff);
        }

        firstParameter = false;
      }
    }

    return buf;
  }

  public static Exprent unboxIfNeeded(Exprent param) {
    // "unbox" invocation parameters, e.g. 'byteSet.add((byte)123)' or 'new ShortContainer((short)813)'
    if (param.type == Exprent.EXPRENT_INVOCATION) {
      InvocationExprent invoc = (InvocationExprent)param;
      if (invoc.isBoxingCall() && !invoc.forceBoxing) {
        param = invoc.lstParameters.get(0);
      }
    }
    return param;
  }

  private boolean isVarArgCall() {
    StructClass cl = DecompilerContext.getStructContext().getClass(classname);
    if (cl != null) {
      StructMethod mt = cl.getMethod(InterpreterUtil.makeUniqueKey(name, stringDescriptor));
      if (mt != null) {
        return mt.hasModifier(CodeConstants.ACC_VARARGS);
      }
    }
    else {
      // TODO: tap into IDEA indices to access libraries methods details

      // try to check the class on the classpath
      Method mtd = ClasspathHelper.findMethod(classname, name, descriptor);
      return mtd != null && mtd.isVarArgs();
    }
    return false;
  }

  private boolean isBoxingCall() {
    if (isStatic && "valueOf".equals(name) && lstParameters.size() == 1) {
      int paramType = lstParameters.get(0).getExprType().type;

      // special handling for ambiguous types
      if (lstParameters.get(0).type == Exprent.EXPRENT_CONST) {
        // 'Integer.valueOf(1)' has '1' type detected as TYPE_BYTECHAR
        // 'Integer.valueOf(40_000)' has '40_000' type detected as TYPE_CHAR
        // so we check the type family instead
        if (lstParameters.get(0).getExprType().typeFamily == CodeConstants.TYPE_FAMILY_INTEGER) {
          if (classname.equals("java/lang/Integer")) {
            return true;
          }
        }

        if (paramType == CodeConstants.TYPE_BYTECHAR || paramType == CodeConstants.TYPE_SHORTCHAR) {
          if (classname.equals("java/lang/Character") || classname.equals("java/lang/Short")) {
            return true;
          }
        }
      }

      return classname.equals(getClassNameForPrimitiveType(paramType));
    }

    return false;
  }

  public void markUsingBoxingResult() {
    canIgnoreBoxing = false;
  }

  // TODO: move to CodeConstants ???
  private static String getClassNameForPrimitiveType(int type) {
    switch (type) {
      case CodeConstants.TYPE_BOOLEAN:
        return "java/lang/Boolean";
      case CodeConstants.TYPE_BYTE:
      case CodeConstants.TYPE_BYTECHAR:
        return "java/lang/Byte";
      case CodeConstants.TYPE_CHAR:
        return "java/lang/Character";
      case CodeConstants.TYPE_SHORT:
      case CodeConstants.TYPE_SHORTCHAR:
        return "java/lang/Short";
      case CodeConstants.TYPE_INT:
        return "java/lang/Integer";
      case CodeConstants.TYPE_LONG:
        return "java/lang/Long";
      case CodeConstants.TYPE_FLOAT:
        return "java/lang/Float";
      case CodeConstants.TYPE_DOUBLE:
        return "java/lang/Double";
    }
    return null;
  }

  private static final Map<String, String> UNBOXING_METHODS;

  static {
    UNBOXING_METHODS = new HashMap<>();
    UNBOXING_METHODS.put("booleanValue", "java/lang/Boolean");
    UNBOXING_METHODS.put("byteValue", "java/lang/Byte");
    UNBOXING_METHODS.put("shortValue", "java/lang/Short");
    UNBOXING_METHODS.put("intValue", "java/lang/Integer");
    UNBOXING_METHODS.put("longValue", "java/lang/Long");
    UNBOXING_METHODS.put("floatValue", "java/lang/Float");
    UNBOXING_METHODS.put("doubleValue", "java/lang/Double");
    UNBOXING_METHODS.put("charValue", "java/lang/Character");
  }

  public boolean isUnboxingCall() {
    return !isStatic && lstParameters.size() == 0 && classname.equals(UNBOXING_METHODS.get(name));
  }

  private List<StructMethod> getMatchedDescriptors() {
    List<StructMethod> matches = new ArrayList<>();
    StructClass currCls = ((ClassNode)DecompilerContext.getProperty(DecompilerContext.CURRENT_CLASS_NODE)).classStruct;
    StructClass cl = DecompilerContext.getStructContext().getClass(classname);
    if (cl == null) return matches;

    Set<String> visited = new HashSet<>();
    Queue<StructClass> que = new ArrayDeque<>();
    que.add(cl);

    while (!que.isEmpty()) {
      StructClass cls = que.poll();
      if (cls == null)
          continue;

      for (StructMethod mt : cls.getMethods()) {
        if (name.equals(mt.getName())) {
          MethodDescriptor md = MethodDescriptor.parseDescriptor(mt.getDescriptor());
          if (matches(md.params, descriptor.params) && canAccess(currCls, mt)) {
            matches.add(mt);
          }
        }
      }

      if (cls == cl && !matches.isEmpty()) {
        return matches;
      }

      visited.add(cls.qualifiedName);
      if (cls.superClass != null && !visited.contains(cls.superClass.value)) {
        StructClass tmp = DecompilerContext.getStructContext().getClass((String)cls.superClass.value);
        if (tmp != null) {
          que.add(tmp);
        }
      }

      for (String intf : cls.getInterfaceNames()) {
        if (!visited.contains(intf)) {
          StructClass tmp = DecompilerContext.getStructContext().getClass(intf);
          if (tmp != null) {
            que.add(tmp);
          }
        }
      }

    }

    return matches;
  }

  private boolean matches(VarType[] left, VarType[] right) {
    if (left.length == right.length) {
      for (int i = 0; i < left.length; i++) {
        if (left[i].typeFamily != right[i].typeFamily) {
          return false;
        }
      }
      return true;
    }
    return false;
  }

  private boolean canAccess(StructClass currCls, StructMethod mt) {
    if (mt.hasModifier(CodeConstants.ACC_PUBLIC)) {
      return true;
    }
    else if (mt.hasModifier(CodeConstants.ACC_PRIVATE)) {
      return mt.getClassStruct().qualifiedName.equals(currCls.qualifiedName);
    }
    else if (mt.hasModifier(CodeConstants.ACC_PROTECTED)) {
      boolean samePackage = isInSamePackage(currCls.qualifiedName, mt.getClassStruct().qualifiedName);
      return samePackage || DecompilerContext.getStructContext().instanceOf(currCls.qualifiedName, mt.getClassStruct().qualifiedName);
    }
    else {
      return isInSamePackage(currCls.qualifiedName, mt.getClassStruct().qualifiedName);
    }
  }

  private boolean isInSamePackage(String class1, String class2) {
    int pos1 = class1.lastIndexOf('/');
    int pos2 = class2.lastIndexOf('/');
    if (pos1 != pos2) {
      return false;
    }

    if (pos1 == -1) {
      return true;
    }

    String pkg1 = class1.substring(0, pos1);
    String pkg2 = class2.substring(0, pos2);
    return pkg1.equals(pkg2);
  }

  private BitSet getAmbiguousParameters(List<StructMethod> matches) {
    StructClass cl = DecompilerContext.getStructContext().getClass(classname);
    if (cl == null || matches.size() == 1) {
      return EMPTY_BIT_SET;
    }

    BitSet missed = new BitSet(lstParameters.size());

    // check if a call is unambiguous
    StructMethod mt = cl.getMethod(InterpreterUtil.makeUniqueKey(name, stringDescriptor));
    if (mt != null) {
      MethodDescriptor md = MethodDescriptor.parseDescriptor(mt.getDescriptor());
      if (md.params.length == lstParameters.size()) {
        boolean exact = true;
        for (int i = 0; i < md.params.length; i++) {
          Exprent exp = lstParameters.get(i);
          if (!md.params[i].equals(exp.getExprType()) || (exp.type == EXPRENT_NEW && ((NewExprent)exp).isLambda() && !((NewExprent)exp).isMethodReference())) {
            exact = false;
            missed.set(i);
          }
        }
        if (exact) return EMPTY_BIT_SET;
      }
    }

    List<StructMethod> mtds = new ArrayList<>();
    for (StructMethod mtt : matches) {
      boolean failed = false;
      MethodDescriptor md = MethodDescriptor.parseDescriptor(mtt.getDescriptor());
      for (int i = 0; i < lstParameters.size(); i++) {
        Exprent exp = lstParameters.get(i);
        VarType ptype = exp.getExprType();
        if (!missed.get(i)) {
          if (!md.params[i].equals(ptype)) {
            failed = true;
            break;
          }
        }
        else {
          if (exp.type == EXPRENT_NEW) {
            NewExprent newExp = (NewExprent)exp;
            if (newExp.isLambda() && !newExp.isMethodReference() && !DecompilerContext.getStructContext().instanceOf(md.params[i].value, exp.getExprType().value)) {
              StructClass pcls = DecompilerContext.getStructContext().getClass(md.params[i].value);
              if (pcls != null && pcls.getMethod(newExp.getLambdaMethodKey()) == null) {
                failed = true;
                break;
              }
              continue;
            }
          }
          if (md.params[i].type == CodeConstants.TYPE_OBJECT) {
            if (ptype.type != CodeConstants.TYPE_NULL) {
              if (!DecompilerContext.getStructContext().instanceOf(ptype.value, md.params[i].value)) {
                failed = true;
                break;
              }
            }
          }
        }
      }
      if (!failed) {
        mtds.add(mtt);
      }
    }
    //TODO: This still causes issues in the case of:
    //add(Object)
    //add(Object...)
    //Try and detect varargs/array?

    // mark parameters
    BitSet ambiguous = new BitSet(descriptor.params.length);
    for (int i = 0; i < descriptor.params.length; i++) {
      VarType paramType = descriptor.params[i];
      for (StructMethod mtt : mtds) {

        GenericMethodDescriptor gen = mtt.getSignature(); //TODO: Find synthetic flags for params, as Enum generic signatures do no contain the String,int params
        if (gen != null && gen.parameterTypes.size() > i && gen.parameterTypes.get(i).isGeneric()) {
          Exprent exp = lstParameters.get(i);
          if (exp.type != EXPRENT_NEW || !((NewExprent)exp).isLambda() || ((NewExprent)exp).isMethodReference()) {
            break;
          }
        }

        MethodDescriptor md = MethodDescriptor.parseDescriptor(mtt.getDescriptor());
        if (!paramType.equals(md.params[i])) {
          ambiguous.set(i);
          break;
        }
      }
    }
    return ambiguous;
  }

  private void processGenericMapping(VarType from, VarType to, Map<VarType, List<VarType>> named, Map<VarType, List<VarType>> bounds) {
    if (VarType.VARTYPE_NULL.equals(to) || (to != null && to.type == CodeConstants.TYPE_GENVAR && !named.containsKey(to))) {
      return;
    }

    VarType current = genericsMap.get(from);
    if (!genericsMap.containsKey(from)) {
      putGenericMapping(from, to, named, bounds);
    }
    else if (to != null && current != null && !to.equals(current)) {
      if (named.containsKey(current)) {
        return;
      }

      if (current.type != CodeConstants.TYPE_GENVAR && to.type == CodeConstants.TYPE_GENVAR) {
        if (named.containsKey(to)) {
          VarType bound = named.get(to).get(0);
          if (!bound.equals(VarType.VARTYPE_OBJECT) && DecompilerContext.getStructContext().instanceOf(bound.value, current.value)) {
            return;
          }
        }
      }

      int wildcard = from.isGeneric() ? ((GenericType)from).getWildcard() : GenericType.WILDCARD_NO;
      if (wildcard == GenericType.WILDCARD_NO || wildcard == GenericType.WILDCARD_EXTENDS) {
        if (!DecompilerContext.getStructContext().instanceOf(to.value, current.value)) {
          if (current.type != CodeConstants.TYPE_GENVAR && to.type != CodeConstants.TYPE_GENVAR) {
            StructClass commonCls = DecompilerContext.getStructContext().getFirstCommonClass(to.value, current.value);
            if (commonCls == null) {
              return; // uh... what?
            }
            else if (!commonCls.qualifiedName.equals(VarType.VARTYPE_OBJECT.value)) {
              to = new VarType(to.type, to.arrayDim, commonCls.qualifiedName);
            }
          }
          putGenericMapping(from, to, named, bounds);
        }
      }
      else if (wildcard == GenericType.WILDCARD_SUPER) {
        if (!DecompilerContext.getStructContext().instanceOf(current.value, to.value)) {
          putGenericMapping(from, to, named, bounds);
        }
      }
    }
  }

  private void putGenericMapping(VarType from, VarType to, Map<VarType, List<VarType>> named, Map<VarType, List<VarType>> bounds) {
    if (isMappingInBounds(from, to, named, bounds)) {
      from = new GenericType(from.type, from.arrayDim, from.value, null, new ArrayList<>(), GenericType.WILDCARD_NO);
      genericsMap.put(from, to);
    }
  }

  private boolean isMappingInBounds(VarType from, VarType to, Map<VarType, List<VarType>> named, Map<VarType, List<VarType>> bounds) {
    if (!bounds.containsKey(from)) {
      return false;
    }

    if (to == null || (to.type == CodeConstants.TYPE_GENVAR && !named.containsKey(to))) {
      return bounds.get(from).get(0).equals(VarType.VARTYPE_OBJECT);
    }

    if (to.type == CodeConstants.TYPE_GENVAR) {
      return isMappingInBounds(from, named.get(to).get(0), named, bounds);
    }

    VarType bound = bounds.get(from).get(0);
    if (bound.type == CodeConstants.TYPE_GENVAR) {
      if (genericsMap.containsKey(bound) && !genericsMap.get(bound).equals(bound)) {
        while (bound != null && genericsMap.containsKey(bound)) {
          bound = genericsMap.get(bound);
        }

        if (bound == null) {
          return false;
        }

        if (bound.type != CodeConstants.TYPE_GENVAR) {
          return DecompilerContext.getStructContext().instanceOf(to.value, bound.value);
        }
      }

      return isMappingInBounds(bound, to, named, bounds);
    }

    if (to.type < CodeConstants.TYPE_OBJECT) {
      return bound.equals(VarType.VARTYPE_OBJECT) || bound.equals(to);
    }

    if (!DecompilerContext.getStructContext().instanceOf(to.value, bound.value)) {
      return false;
    }

    if (bound.isGeneric() && !((GenericType)bound).getArguments().isEmpty()) {
      GenericType genbound = (GenericType)bound;
      VarType _new = to;

      if (!to.value.equals(bound.value)) {
        _new = GenericType.getGenericSuperType(to, bound);
      }

      if (!_new.isGeneric() || ((GenericType)_new).getArguments().size() != genbound.getArguments().size()) {
        return false;
      }

      GenericType genNew = (GenericType)_new;
      for (int i = 0; i < genbound.getArguments().size(); ++i) {
        VarType boundArg = genbound.getArguments().get(i);
        VarType newArg = genNew.getArguments().get(i);

        if (boundArg == null) {
          continue;
        }

        if (!boundArg.equals(newArg)) {
          // T extends Comparable<T>
          if (boundArg.equals(from) && newArg.equals(to)) {
            continue;
          }

          // T extends Comparable<S>, S extends Object
          if (bounds.containsKey(boundArg) && isMappingInBounds(boundArg, newArg, named, bounds)) {
            continue;
          }
          return false;
        }
      }
    }
    return true;
  }

  private Map<VarType, List<VarType>> getGenericBounds(StructClass mthCls) {
    Map<VarType, List<VarType>> bounds = new HashMap<>();

    if (desc.getSignature() != null) {
      for (int x = 0; x < desc.getSignature().typeParameters.size(); x++) {
        bounds.put(GenericType.parse("T" + desc.getSignature().typeParameters.get(x) + ";"), desc.getSignature().typeParameterBounds.get(x));
      }
    }

    if (mthCls.getSignature() != null) {
      for (int x = 0; x < mthCls.getSignature().fparameters.size(); x++) {
        bounds.put(GenericType.parse("T" + mthCls.getSignature().fparameters.get(x) + ";"), mthCls.getSignature().fbounds.get(x));
      }
    }

    return bounds;
  }

  @Override
  public void replaceExprent(Exprent oldExpr, Exprent newExpr) {
    if (oldExpr == instance) {
      instance = newExpr;
    }

    for (int i = 0; i < lstParameters.size(); i++) {
      if (oldExpr == lstParameters.get(i)) {
        lstParameters.set(i, newExpr);
      }
    }
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) return true;
    if (o == null || !(o instanceof InvocationExprent)) return false;

    InvocationExprent it = (InvocationExprent)o;
    return InterpreterUtil.equalObjects(name, it.getName()) &&
           InterpreterUtil.equalObjects(classname, it.getClassname()) &&
           isStatic == it.isStatic() &&
           InterpreterUtil.equalObjects(instance, it.getInstance()) &&
           InterpreterUtil.equalObjects(descriptor, it.getDescriptor()) &&
           functype == it.getFunctype() &&
           InterpreterUtil.equalLists(lstParameters, it.getLstParameters());
  }

  public List<Exprent> getLstParameters() {
    return lstParameters;
  }

  public void setLstParameters(List<Exprent> lstParameters) {
    this.lstParameters = lstParameters;
  }

  public MethodDescriptor getDescriptor() {
    return descriptor;
  }

  public void setDescriptor(MethodDescriptor descriptor) {
    this.descriptor = descriptor;
  }

  public String getClassname() {
    return classname;
  }

  public void setClassname(String classname) {
    this.classname = classname;
  }

  public int getFunctype() {
    return functype;
  }

  public void setFunctype(int functype) {
    this.functype = functype;
  }

  public Exprent getInstance() {
    return instance;
  }

  public void setInstance(Exprent instance) {
    this.instance = instance;
  }

  public boolean isStatic() {
    return isStatic;
  }

  public void setStatic(boolean isStatic) {
    this.isStatic = isStatic;
  }

  public String getName() {
    return name;
  }

  public void setName(String name) {
    this.name = name;
  }

  public String getStringDescriptor() {
    return stringDescriptor;
  }

  public void setStringDescriptor(String stringDescriptor) {
    this.stringDescriptor = stringDescriptor;
  }

  public int getInvocationTyp() {
    return invocationTyp;
  }

  public String getInvokeDynamicClassSuffix() {
    return invokeDynamicClassSuffix;
  }

  public List<PooledConstant> getBootstrapArguments() {
    return bootstrapArguments;
  }

  public void setSyntheticGetClass() {
    isSyntheticGetClass = true;
  }

  public boolean isSyntheticGetClass() {
    return isSyntheticGetClass;
  }

  public List<VarType> getGenericArgs() {
    return genericArgs;
  }

  public Map<VarType, VarType> getGenericsMap() {
    return genericsMap;
  }

  public void setInvocationInstance() {
    isInvocationInstance = true;
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    measureBytecode(values, lstParameters);
    measureBytecode(values, instance);
    measureBytecode(values);
  }

  // *****************************************************************************
  // IMatchable implementation
  // *****************************************************************************

  @Override
  public boolean match(MatchNode matchNode, MatchEngine engine) {
    if (!super.match(matchNode, engine)) {
      return false;
    }

    for (Entry<MatchProperties, RuleValue> rule : matchNode.getRules().entrySet()) {
      RuleValue value = rule.getValue();

      MatchProperties key = rule.getKey();
      if (key == MatchProperties.EXPRENT_INVOCATION_PARAMETER) {
        if (value.isVariable() && (value.parameter >= lstParameters.size() ||
                                   !engine.checkAndSetVariableValue(value.value.toString(), lstParameters.get(value.parameter)))) {
          return false;
        }
      }
      else if (key == MatchProperties.EXPRENT_INVOCATION_CLASS) {
        if (!value.value.equals(this.classname)) {
          return false;
        }
      }
      else if (key == MatchProperties.EXPRENT_INVOCATION_SIGNATURE) {
        if (!value.value.equals(this.name + this.stringDescriptor)) {
          return false;
        }
      }
    }

    return true;
  }
}
