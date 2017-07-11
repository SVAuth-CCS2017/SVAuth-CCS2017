using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;

using Bpl = Microsoft.Boogie;
using System.Diagnostics.Contracts;

namespace BytecodeTranslator {

      class RelaxedTypeEquivalenceComparer : IEqualityComparer<ITypeReference> {

      private RelaxedTypeEquivalenceComparer(bool resolveTypes = false) {
        this.resolveTypes = resolveTypes;
      }

      bool resolveTypes;

      /// <summary>
      /// A singleton instance of RelaxedTypeEquivalenceComparer that is safe to use in all contexts.
      /// </summary>
      internal static RelaxedTypeEquivalenceComparer instance = new RelaxedTypeEquivalenceComparer();

      /// <summary>
      /// A singleton instance of RelaxedTypeEquivalenceComparer that is safe to use in all contexts.
      /// </summary>
      internal static RelaxedTypeEquivalenceComparer resolvingInstance = new RelaxedTypeEquivalenceComparer(true);

      /// <summary>
      /// Determines whether the specified objects are equal.
      /// </summary>
      /// <param name="x">The first object to compare.</param>
      /// <param name="y">The second object to compare.</param>
      /// <returns>
      /// true if the specified objects are equal; otherwise, false.
      /// </returns>
      public bool Equals(ITypeReference x, ITypeReference y) {
        if (x == null) return y == null;
        // Type equality done on string names which ignores the dll the type is coming from.  
        // This is done to enable giving models of classes in stubs.
        var xName = TypeHelper.GetTypeName(x);
        var yName = TypeHelper.GetTypeName(y);
        return xName.Equals(yName);
        //var result = TypeHelper.TypesAreEquivalentAssumingGenericMethodParametersAreEquivalentIfTheirIndicesMatch(x, y, this.resolveTypes);
        //return result;
      }

      /// <summary>
      /// Returns a hash code for this instance.
      /// </summary>
      /// <param name="r">The r.</param>
      /// <returns>
      /// A hash code for this instance, suitable for use in hashing algorithms and data structures like a hash table. 
      /// </returns>
      public int GetHashCode(ITypeReference r) {
          var xName = TypeHelper.GetTypeName(r);
          return xName.GetHashCode();
        //return (int)r.InternedKey;
      }

    }

  class WholeProgram : TraverserFactory {

    public override TranslationPlugins.Translator getTranslator(Sink sink, IDictionary<IUnit, IContractProvider> contractProviders, IDictionary<IUnit, PdbReader> pdbReaders) {
      BaseTranslator translator = new BaseTranslator(this, sink, contractProviders, pdbReaders);
      return translator;
    }

    /// <summary>
    /// Table to be filled by the metadata traverser before visiting any assemblies.
    /// 
    /// The table lists the direct supertypes of all type definitions that it encounters during the
    /// traversal. (But the table is organized so that subTypes[T] is the list of type definitions
    /// that are direct subtypes of T.)
    /// </summary>
    readonly public Dictionary<ITypeReference, List<ITypeReference>> subTypes = new Dictionary<ITypeReference, List<ITypeReference>>(RelaxedTypeEquivalenceComparer.resolvingInstance);

    public override BCTMetadataTraverser MakeMetadataTraverser(Sink sink,
      IDictionary<IUnit, IContractProvider> contractProviders, // TODO: remove this parameter?
      IDictionary<IUnit, PdbReader> pdbReaders) {
      return new WholeProgramMetadataSemantics(this, sink, pdbReaders, this);
    }

    public class WholeProgramMetadataSemantics : BCTMetadataTraverser {

      readonly WholeProgram parent;
      readonly Sink sink;

      readonly Dictionary<IUnit, bool> codeUnderAnalysis = new Dictionary<IUnit, bool>();

      public WholeProgramMetadataSemantics(WholeProgram parent, Sink sink, IDictionary<IUnit, PdbReader> pdbReaders, TraverserFactory factory)
        : base(sink, pdbReaders, factory) {
        this.parent = parent;
        this.sink = sink;
      }

      public override void TranslateAssemblies(IEnumerable<IUnit> assemblies) {
        #region traverse all of the units gathering type information
        var typeRecorder = new RecordSubtypes(this.parent.subTypes);
        foreach (var a in assemblies) {
          this.codeUnderAnalysis.Add(a, true);
          typeRecorder.Traverse((IAssembly)a);
        }
        #endregion
        #region Possibly gather exception information
        if (sink.Options.modelExceptions == 1) {
          this.sink.MethodThrowsExceptions = ExceptionAnalyzer.ComputeExplicitlyThrownExceptions(assemblies);
        }
          
        #endregion

        base.TranslateAssemblies(assemblies);
      }
      
      class RecordSubtypes : MetadataTraverser {

        Dictionary<ITypeReference, List<ITypeReference>> subTypes;
        HashSet<uint> visitedTypes;

        public RecordSubtypes(Dictionary<ITypeReference, List<ITypeReference>> subTypes) {
          this.subTypes = subTypes;
          this.visitedTypes = new HashSet<uint>();
        }

        public override void TraverseChildren(ITypeDefinition typeDefinition) {
          if (this.visitedTypes.Contains(typeDefinition.InternedKey)) return;
          this.visitedTypes.Add(typeDefinition.InternedKey);
          ITypeReference tr;
          foreach (var baseClass in typeDefinition.BaseClasses) {
            tr = TypeHelper.UninstantiateAndUnspecialize(baseClass);
            if (!this.subTypes.ContainsKey(tr)) {
              this.subTypes[tr] = new List<ITypeReference>();
            }
            this.subTypes[tr].Add(typeDefinition);
            TraverseChildren(tr.ResolvedType);
          }

          foreach (var iface in typeDefinition.Interfaces) {
            tr = TypeHelper.UninstantiateAndUnspecialize(iface);
            if (!this.subTypes.ContainsKey(tr)) {
              this.subTypes[tr] = new List<ITypeReference>();
            }
            this.subTypes[tr].Add(typeDefinition);
            TraverseChildren(tr.ResolvedType);
          }
          base.Traverse(typeDefinition.NestedTypes);
        }
      }

    }

    public override ExpressionTraverser MakeExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext, bool expressionIsStatement) {
      return new WholeProgramExpressionSemantics(this, sink, statementTraverser, contractContext, expressionIsStatement);
    }

    /// <summary>
    /// implement virtual method calls to methods defined in the CUA (code under analysis, i.e.,
    /// the set of assemblies being translated) by a "switch statement" that dispatches to the
    /// most derived type's method. I.e., make explicit the dynamic dispatch mechanism.
    /// </summary>
    public class WholeProgramExpressionSemantics : CLRSemantics.CLRExpressionSemantics {

      readonly WholeProgram parent;
      readonly public Dictionary<ITypeReference, List<ITypeReference>> subTypes;

      public WholeProgramExpressionSemantics(WholeProgram parent, Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext, bool expressionIsStatement)
        : base(sink, statementTraverser, contractContext, expressionIsStatement) {
        this.parent = parent;
        this.subTypes = parent.subTypes;
      }

      public override void TraverseChildren(IMethodCall methodCall) {
        var resolvedMethod = Sink.Unspecialize(methodCall.MethodToCall).ResolvedMethod;

        var methodName = Microsoft.Cci.MemberHelper.GetMethodSignature(resolvedMethod);
        if (methodName.Equals("System.Object.GetHashCode") || methodName.Equals("System.Object.ToString")) {
          base.TraverseChildren(methodCall);
          return;
        }

        bool isEventAdd = resolvedMethod.IsSpecialName && resolvedMethod.Name.Value.StartsWith("add_");
        bool isEventRemove = resolvedMethod.IsSpecialName && resolvedMethod.Name.Value.StartsWith("remove_");
        if (isEventAdd || isEventRemove) {
          base.TraverseChildren(methodCall);
          return;
        }

        if (!methodCall.IsVirtualCall) {
          base.TraverseChildren(methodCall);
          return;
        }
        var containingType = TypeHelper.UninstantiateAndUnspecialize(methodCall.MethodToCall.ContainingType);
        List<ITypeReference> subTypesOfContainingType;
        if (!this.subTypes.TryGetValue(containingType, out subTypesOfContainingType)) {
          base.TraverseChildren(methodCall);
          return;
        }
        Contract.Assert(0 < subTypesOfContainingType.Count);
        Contract.Assert(!methodCall.IsStaticCall);
        Contract.Assert(!resolvedMethod.IsConstructor);
        var overrides = new Dictionary<ITypeReference, IMethodDefinition>(new InternedKeyComparer());
        FindOverrides(containingType, resolvedMethod, overrides);
        bool same = true;
        foreach (var o in overrides) {
          IMethodDefinition resolvedOverride = Sink.Unspecialize(o.Value).ResolvedMethod;
          if (resolvedOverride != resolvedMethod)
            same = false;
        }
        // The !IsInterface check was breaking a case with one nondeterministic
        // interface extending another.  What was the purpose of the check??
        // ~ REDACTED 2016-06-17
        if (/*!(containingType.ResolvedType.IsInterface) &&*/ (0 == overrides.Count || same)) {
          base.TraverseChildren(methodCall);
          return;
        }

        Contract.Assume(1 <= overrides.Count);

        var getType = new Microsoft.Cci.MethodReference(
          this.sink.host,
          this.sink.host.PlatformType.SystemObject,
          CallingConvention.HasThis,
          this.sink.host.PlatformType.SystemType,
          this.sink.host.NameTable.GetNameFor("GetType"), 0);
        var op_Type_Equality = new Microsoft.Cci.MethodReference(
          this.sink.host,
          this.sink.host.PlatformType.SystemType,
          CallingConvention.Default,
          this.sink.host.PlatformType.SystemBoolean,
          this.sink.host.NameTable.GetNameFor("op_Equality"),
          0,
          this.sink.host.PlatformType.SystemType,
          this.sink.host.PlatformType.SystemType);

        // Depending on whether the method is a void method or not
        // Turn into expression:
        //   (o.GetType() == typeof(T1)) ? ((T1)o).M(...) : ( (o.GetType() == typeof(T2)) ? ((T2)o).M(...) : ...
        // Or turn into statements:
        //   if (o.GetType() == typeof(T1)) ((T1)o).M(...) else if ...
        var turnIntoStatements = resolvedMethod.Type.TypeCode == PrimitiveTypeCode.Void;
        IStatement elseStatement = null;

        IExpression elseValue = new MethodCall() {
          Arguments = new List<IExpression>(methodCall.Arguments),
          IsStaticCall = false,
          IsVirtualCall = false,
          MethodToCall = methodCall.MethodToCall,
          ThisArgument = methodCall.ThisArgument,
          Type = methodCall.Type,
        };
        if (turnIntoStatements)
          elseStatement = new ExpressionStatement() { Expression = elseValue, };

        Conditional ifConditional = null;
        ConditionalStatement ifStatement = null;

        foreach (var typeMethodPair in overrides) {
          var t = typeMethodPair.Key;
          IMethodReference m = typeMethodPair.Value;

          if (m.IsGeneric) {
            var baseMethod = m.ResolvedMethod;
            m = new GenericMethodInstanceReference() {
              CallingConvention = baseMethod.CallingConvention,
              ContainingType = baseMethod.ContainingTypeDefinition,
              GenericArguments = new List<ITypeReference>(IteratorHelper.GetConversionEnumerable<IGenericMethodParameter, ITypeReference>(baseMethod.GenericParameters)),
              GenericMethod = baseMethod,
              InternFactory = this.sink.host.InternFactory,
              Name = baseMethod.Name,
              Parameters = baseMethod.ParameterCount == 0 ? null : new List<IParameterTypeInformation>(baseMethod.Parameters),
              Type = baseMethod.Type,
            };
          }

          // .NET Core does not have System.Type.op_Equality; just do a
          // reference equality test.  TODO: conditionalize this for upstreaming
          // to BCT. ~ REDACTED 2016-06-15
#if false
          var cond = new MethodCall() {
            Arguments = new List<IExpression>(){
                new MethodCall() {
                  Arguments = new List<IExpression>(),
                  IsStaticCall = false,
                  IsVirtualCall = false,
                  MethodToCall = getType,
                  ThisArgument = methodCall.ThisArgument,
                },
                new TypeOf() {
                  TypeToGet = t,
                },
              },
            IsStaticCall = true,
            IsVirtualCall = false,
            MethodToCall = op_Type_Equality,
            Type = this.sink.host.PlatformType.SystemBoolean,
          };
#endif
          var cond = new Equality() {
            LeftOperand = new MethodCall() {
              Arguments = new List<IExpression>(),
              IsStaticCall = false,
              IsVirtualCall = false,
              MethodToCall = getType,
              ThisArgument = methodCall.ThisArgument,
            },
            RightOperand = new TypeOf() {
              TypeToGet = t,
            },
          };
          Expression thenValue = new MethodCall() {
            Arguments = new List<IExpression>(methodCall.Arguments),
            IsStaticCall = false,
            IsVirtualCall = false,
            MethodToCall = m,
            ThisArgument = methodCall.ThisArgument,
            Type = m.Type,
          };
          thenValue = new Conversion() {
            Type = m.Type,
            TypeAfterConversion = methodCall.Type,
            ValueToConvert = thenValue,
          };
          if (turnIntoStatements) {
            ifStatement = new ConditionalStatement() {
              Condition = cond,
              FalseBranch = elseStatement,
              TrueBranch = new ExpressionStatement() { Expression = thenValue, },
            };
            elseStatement = ifStatement;
          } else {
            ifConditional = new Conditional() {
              Condition = cond,
              ResultIfFalse = elseValue,
              ResultIfTrue = thenValue,
            };
            elseValue = ifConditional;
          }
        }
        if (turnIntoStatements) {
          Contract.Assume(ifStatement != null);
          this.StmtTraverser.Traverse(ifStatement);
        } else {
          Contract.Assume(ifConditional != null);
          base.Traverse(ifConditional);
        }

        return;
      }

      private void FindImplementations(ITypeDefinition type, IMethodDefinition interfaceMethod, Dictionary<ITypeReference, IMethodDefinition> implementations) {
        // There can be multiple paths to the same class or interface, so avoid
        // duplicate traversal.  We use null values for interfaces and for
        // classes that don't have an implementation.
        if (implementations.ContainsKey(type))
          return;
        if (type.IsInterface)
        {
          // Handle indirect interfaces.  Normally this shouldn't be needed
          // because C# converts transitive interfaces to direct ones.
          implementations.Add(type, null);
          foreach (var subType in this.subTypes[type])
          {
            FindImplementations(subType.ResolvedType, interfaceMethod, implementations);
          }
        }
        else
        {
          // prefer explicit, since if both are there, only the implicit get called through the iface pointer.
          IMethodDefinition foundMethod = null;
          foreach (var implementingMethod in GetExplicitlyImplementedMethods(type, interfaceMethod))
          {
            foundMethod = implementingMethod;
          }
          if (foundMethod == null)
          { // look for implicit
            var mems = type.GetMatchingMembersNamed(interfaceMethod.Name, true,
              tdm => {
                var m = tdm as IMethodDefinition;
                if (m == null) return false;
                return TypeHelper.ParameterListsAreEquivalentAssumingGenericMethodParametersAreEquivalentIfTheirIndicesMatch(
                  m.Parameters, interfaceMethod.Parameters);
              });
            foreach (var mem in mems)
            {
              var methodDef = mem as IMethodDefinition;
              if (methodDef == null) continue;
              foundMethod = methodDef;
            }
          }
          // If foundMethod is still null, the method may come from a superclass
          // that implements the same interface.  (XXX: Check that this is the
          // case so we find out if we missed any other cases?)
          implementations.Add(type, foundMethod);
        }
      }

      /// <summary>
      /// Modifies <paramref name="overrides"/> as side-effect.
      /// </summary>
      private void FindOverrides(ITypeReference type, IMethodDefinition originalResolvedMethod, Dictionary<ITypeReference, IMethodDefinition> overrides) {
        Contract.Requires(type != null);
        Contract.Requires(originalResolvedMethod != null);
        if (originalResolvedMethod.ContainingTypeDefinition.IsInterface) {
          /* Even if we ignore generics, the CLI rules for interface mapping are
           * very complicated, and I've seen some phenomena that I don't fully
           * understand.  So I'm choosing an algorithm that is relatively easy
           * to implement and will hopefully be correct for most of the code
           * people actually want to analyze.  Unfortunately, even stating a
           * simple set of conditions under which this algorithm matches the
           * CLI behavior seems to be hard.
           *
           * Summary:
           * 1. Find each class that is declared to implement the interface,
           *    either directly or via other interfaces (not superclasses), and
           *    check for an explicit or implicit implementation defined in the
           *    same class (not inherited from a superclass).  If there is none,
           *    ignore the class; it's probably reusing the mapping from an
           *    ancestor class that already implements the interface, and we'll
           *    process that in step 2.
           * 2. From each implementation found, traverse subclasses and make
           *    them dispatch to the same implementation or an override if they
           *    have one.  (Explicit implementations normally can't be
           *    overridden.)  Don't traverse subclasses that have their own
           *    implementations found in step 1.
           *
           * ~ REDACTED 2016-08-06 */

          // Step 1
          var implementations = new Dictionary<ITypeReference, IMethodDefinition>(new InternedKeyComparer());
          FindImplementations(type.ResolvedType, originalResolvedMethod, implementations);

          // Add all implementations to the overrides dict up front so that
          // step-2 traversal stops when it reaches another implementation, even
          // if we haven't processed that implementation yet.
          foreach (var implementation in implementations)
          {
            if (implementation.Value != null)
            {
              overrides.Add(implementation.Key, implementation.Value);
            }
          }

          // Step 2.  FindOverrides should be smart enough to know that explicit
          // implementations can't be overridden because they're private, in
          // which case it's just an easy way to dispatch all subclasses to the
          // same explicit implementation.
          foreach (var implementation in implementations)
          {
            if (implementation.Value != null)
            {
              FindOverrides(implementation.Key, implementation.Value, overrides);
            }
          }
        } else {
          List<ITypeReference> subTypes;
          if (!this.subTypes.TryGetValue(type, out subTypes))
            return;
          foreach (var subType in subTypes) {
            if (overrides.ContainsKey(subType))
            {
              // This can happen when the original method belongs to an
              // interface and subType has its own implementation.  Don't
              // traverse into subType.
              continue;
            }
            // XXX: On recursive calls to FindOverrides, subType may be an
            // indirect subtype of resolvedMethod.ContainingType, and it looks
            // like GetImplicitlyOverridingDerivedClassMethod is not designed to
            // check for newslot along the entire path in that case.
            var methodForSubtype = MemberHelper.GetImplicitlyOverridingDerivedClassMethod(originalResolvedMethod, subType.ResolvedType);
            if (methodForSubtype == Dummy.Method) {
              methodForSubtype = originalResolvedMethod;
            }
            overrides.Add(subType, methodForSubtype);
            FindOverrides(subType, methodForSubtype, overrides);
          }
        }
      }

      /// <summary>
      /// Returns zero or more explicit implementations of an interface method that are defined in the given type definition.
      /// </summary>
      public static IEnumerable<IMethodDefinition> GetExplicitlyImplementedMethods(ITypeDefinition typeDefinition, IMethodDefinition ifaceMethod) {
        Contract.Requires(ifaceMethod != null);
        Contract.Ensures(Contract.Result<IEnumerable<IMethodReference>>() != null);
        Contract.Ensures(Contract.ForAll(Contract.Result<IEnumerable<IMethodReference>>(), x => x != null));

        foreach (IMethodImplementation methodImplementation in typeDefinition.ExplicitImplementationOverrides) {
          var implementedInterfaceMethod = MemberHelper.UninstantiateAndUnspecialize(methodImplementation.ImplementedMethod);
          if (ifaceMethod.InternedKey == implementedInterfaceMethod.InternedKey)
            yield return methodImplementation.ImplementingMethod.ResolvedMethod;
        }
        var mems = TypeHelper.GetMethod(typeDefinition, ifaceMethod.Name, ifaceMethod.Parameters.Select(p => p.Type).ToArray());
      }


    }

  }
}
