//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
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
using TranslationPlugins;


namespace BytecodeTranslator
{
  public class MostNestedTryStatementTraverser : CodeTraverser {
    Dictionary<IName, ITryCatchFinallyStatement> mostNestedTryStatement = new Dictionary<IName, ITryCatchFinallyStatement>();
    ITryCatchFinallyStatement currStatement = null;
    public override void TraverseChildren(ILabeledStatement labeledStatement) {
      if (currStatement != null)
        mostNestedTryStatement.Add(labeledStatement.Label, currStatement);
      base.TraverseChildren(labeledStatement);
    }
    public override void TraverseChildren(ITryCatchFinallyStatement tryCatchFinallyStatement) {
      ITryCatchFinallyStatement savedStatement = currStatement;
      currStatement = tryCatchFinallyStatement;
      base.TraverseChildren(tryCatchFinallyStatement);
      currStatement = savedStatement;
    }
    public ITryCatchFinallyStatement MostNestedTryStatement(IName label) {
      if (!mostNestedTryStatement.ContainsKey(label))
        return null;
      return mostNestedTryStatement[label];
    }
  }

  public class StatementTraverser : CodeTraverser {

    public readonly TraverserFactory factory;

    readonly Sink sink;

    public readonly PdbReader/*?*/ PdbReader;

    public readonly Bpl.StmtListBuilder StmtBuilder = new Bpl.StmtListBuilder();
    private SourceContextEmitter sourceContextEmitter;
    private bool contractContext;
    private bool captureState;
    private static int captureStateCounter = 0;
    public IPrimarySourceLocation lastSourceLocation;

    #region Constructors
    public StatementTraverser(Sink sink, PdbReader/*?*/ pdbReader, bool contractContext, TraverserFactory factory) {
      this.sink = sink;
      this.factory = factory;
      PdbReader = pdbReader;
      this.contractContext = contractContext;
      this.captureState = sink.Options.captureState;
      this.sourceContextEmitter = new SourceContextEmitter(this);
      this.PreorderVisitor = sourceContextEmitter;
    }
    #endregion

    #region Helper Methods

    Bpl.Expr ExpressionFor(IExpression expression) {
      ExpressionTraverser etrav = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      etrav.Traverse(expression);
      Contract.Assert(etrav.TranslatedExpressions.Count == 1);
      return etrav.TranslatedExpressions.Pop();
    }

    public ICollection<ITypeDefinition>/*?*/ TranslateMethod(IMethodDefinition method) {
      // Let an exception be thrown if this is not as expected.
      var methodBody = (ISourceMethodBody)method.Body;
      var block = (BlockStatement)methodBody.Block;

      ICollection<ITypeDefinition> newTypes = null;
      if (block != null) {
        var remover = new AnonymousDelegateRemover(this.sink.host, this.PdbReader);
        newTypes = remover.RemoveAnonymousDelegates(methodBody.MethodDefinition, block);
      }
      StmtBuilder.Add(new Bpl.AssumeCmd(Bpl.Token.NoToken, Bpl.Expr.True, new Bpl.QKeyValue(Bpl.Token.NoToken, "breadcrumb", new List<object> { Bpl.Expr.Literal(this.sink.UniqueNumberAcrossAllAssemblies) }, null)));
      this.Traverse(methodBody);
      return newTypes;
    }
    #endregion

    #region Helper Classes
    class SourceContextEmitter : CodeVisitor {
      StatementTraverser parent;
      public SourceContextEmitter(StatementTraverser parent) {
        this.parent = parent;
      }

      public override void Visit(IStatement statement) {
        this.parent.EmitSourceContext(statement);
        if (this.parent.sink.Options.captureState) {
          var tok = statement.Token();
          var state = String.Format("s{0}", StatementTraverser.captureStateCounter++);
          var attrib = new Bpl.QKeyValue(tok, "captureState ", new List<object> { state }, null);
          this.parent.StmtBuilder.Add(
            new Bpl.AssumeCmd(tok, Bpl.Expr.True, attrib)
            );
        }
      }
    }
    #endregion

    //public override void Visit(ISourceMethodBody methodBody) {
    //  var block = methodBody.Block as BlockStatement;
    //  // TODO: Error if cast fails?

    //  if (block != null) {
    //    var remover = new AnonymousDelegateRemover(this.sink.host, this.PdbReader);
    //    var newTypes = remover.RemoveAnonymousDelegates(methodBody.MethodDefinition, block);
    //  }
    //  base.Visit(methodBody);
    //}

    public override void TraverseChildren(IBlockStatement block) {
      foreach (var s in block.Statements) {
        this.Traverse(s);
      }
    }

    public void EmitSourceContext(IObjectWithLocations element) {
      if (element is IEmptyStatement) return;
      var tok = element.Token();
      string fileName = null;
      int lineNumber = 0;
      if (this.PdbReader != null)
      {
        var slocs = this.PdbReader.GetClosestPrimarySourceLocationsFor(element.Locations);
        foreach (var sloc in slocs)
        {
          fileName = sloc.Document.Location;
          lineNumber = sloc.StartLine;

          this.lastSourceLocation = sloc;
          break;
        }
        if (fileName != null)
        {
          var attrib = new Bpl.QKeyValue(tok, "sourceLine", new List<object> { Bpl.Expr.Literal((int)lineNumber) }, null);
          attrib = new Bpl.QKeyValue(tok, "sourceFile", new List<object> { fileName }, attrib);
          attrib = new Bpl.QKeyValue(tok, "first", new List<object>(), attrib);
          this.StmtBuilder.Add(
            new Bpl.AssertCmd(tok, Bpl.Expr.True, attrib)
            );
        }
      }
    }

    public void EmitSecondaryLineDirective(Bpl.IToken methodCallToken) {
      var sloc = this.lastSourceLocation;
      if (sloc != null)
      {
        var fileName = sloc.Document.Location;
        var lineNumber = sloc.StartLine;
        var attrib = new Bpl.QKeyValue(methodCallToken, "sourceLine", new List<object> { Bpl.Expr.Literal((int)lineNumber) }, null);
        attrib = new Bpl.QKeyValue(methodCallToken, "sourceFile", new List<object> { fileName }, attrib);
        this.StmtBuilder.Add(new Bpl.AssertCmd(methodCallToken, Bpl.Expr.True, attrib));
      }
    }

    public void AddRecordCall(string label, IExpression value, Bpl.Expr valueBpl) {
      // valueBpl.Type only gets set in a few simple cases, while
      // sink.CciTypeToBoogie(value.Type.ResolvedType) should always be correct
      // if BCT is working properly. *cross fingers*
      // ~ REDACTED 2016-06-21
      AddRecordCall(label, sink.CciTypeToBoogie(value.Type.ResolvedType), valueBpl);
    }
    public void AddRecordCall(string label, Bpl.Type typeBpl, Bpl.Expr valueBpl) {

      /* Without this, some record calls show up on the wrong source lines in
       * the Corral trace or don't show up at all.  With it, the number of extra
       * blank lines in the trace increases in some cases but not in others.  I
       * think we're better off with this line.  TODO: understand how Corral
       * line directives are actually supposed to be used.
       * ~ REDACTED 2016-07-08 */
      EmitSecondaryLineDirective(Bpl.Token.NoToken);

      var logProcedureName = sink.FindOrCreateRecordProcedure(typeBpl);
      var call = new Bpl.CallCmd(Bpl.Token.NoToken, logProcedureName, new List<Bpl.Expr> { valueBpl }, new List<Bpl.IdentifierExpr> { });
      // This seems to be the idiom (see Bpl.Program.addUniqueCallAttr).
      // XXX What does the token mean?  Should there be one?
      // ~ REDACTED 2016-06-13
      call.Attributes = new Bpl.QKeyValue(Bpl.Token.NoToken, "cexpr", new List<object> { label }, call.Attributes);
      StmtBuilder.Add(call);
    }

    #region Basic Statements

    public override void TraverseChildren(IAssertStatement assertStatement) {
      Bpl.Expr conditionExpr = ExpressionFor(assertStatement.Condition);
      Bpl.Type conditionType = this.sink.CciTypeToBoogie(assertStatement.Condition.Type);
      if (conditionType == this.sink.Heap.RefType) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Ident(this.sink.Heap.NullRef));
      }
      else if (conditionType == Bpl.Type.Int) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Literal(0));
      }
      else {
        System.Diagnostics.Debug.Assert(conditionType == Bpl.Type.Bool);
      }
      if (this.sink.Options.getMeHere) {
        StmtBuilder.Add(new Bpl.AssumeCmd(assertStatement.Token(), conditionExpr));
      } else {
        StmtBuilder.Add(new Bpl.AssertCmd(assertStatement.Token(), conditionExpr));
      }
    }

    public override void TraverseChildren(IAssumeStatement assumeStatement) {
      Bpl.Expr conditionExpr = ExpressionFor(assumeStatement.Condition);
      Bpl.Type conditionType = this.sink.CciTypeToBoogie(assumeStatement.Condition.Type);
      if (conditionType == this.sink.Heap.RefType) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Ident(this.sink.Heap.NullRef));
      }
      else if (conditionType == Bpl.Type.Int) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Literal(0));
      }
      else {
        System.Diagnostics.Debug.Assert(conditionType == Bpl.Type.Bool);
      }
      StmtBuilder.Add(new Bpl.AssumeCmd(assumeStatement.Token(), conditionExpr));
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) Works, but still a stub</remarks>
    /// <param name="conditionalStatement"></param>
    public override void TraverseChildren(IConditionalStatement conditionalStatement) {
      StatementTraverser thenTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext);
      StatementTraverser elseTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext);
      ExpressionTraverser condTraverser = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);

      if (this.sink.Options.instrumentBranches) {
        var tok = conditionalStatement.Token();
        thenTraverser.StmtBuilder.Add(
          new Bpl.AssumeCmd(tok, Bpl.Expr.True, new Bpl.QKeyValue(Bpl.Token.NoToken, "breadcrumb", new List<object> { Bpl.Expr.Literal(this.sink.UniqueNumberAcrossAllAssemblies) }, null))
          );
        elseTraverser.StmtBuilder.Add(
          new Bpl.AssumeCmd(tok, Bpl.Expr.True, new Bpl.QKeyValue(Bpl.Token.NoToken, "breadcrumb", new List<object> { Bpl.Expr.Literal(this.sink.UniqueNumberAcrossAllAssemblies) }, null))
          );
      }

      condTraverser.Traverse(conditionalStatement.Condition);
      thenTraverser.Traverse(conditionalStatement.TrueBranch);
      elseTraverser.Traverse(conditionalStatement.FalseBranch);

      Bpl.Expr conditionExpr = condTraverser.TranslatedExpressions.Pop();
      Bpl.Type conditionType = this.sink.CciTypeToBoogie(conditionalStatement.Condition.Type);
      if (conditionType == this.sink.Heap.RefType) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Ident(this.sink.Heap.NullRef));
      }
      else if (conditionType == Bpl.Type.Int) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Literal(0));
      }
      else {
        System.Diagnostics.Debug.Assert(conditionType == Bpl.Type.Bool);
      }

      Bpl.IfCmd ifcmd = new Bpl.IfCmd(conditionalStatement.Token(),
          conditionExpr,
          thenTraverser.StmtBuilder.Collect(conditionalStatement.TrueBranch.Token()),
          null,
          elseTraverser.StmtBuilder.Collect(conditionalStatement.FalseBranch.Token())
          );

      StmtBuilder.Add(ifcmd);

    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="expressionStatement"></param>
    /// <remarks> TODO: might be wrong for the general case</remarks>
    public override void TraverseChildren(IExpressionStatement expressionStatement) {

      var expressionIsOpAssignStatement = false;
      var binOp = expressionStatement.Expression as IBinaryOperation;
      if (binOp != null && binOp.LeftOperand is ITargetExpression)
          expressionIsOpAssignStatement = true;

      ExpressionTraverser etrav = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext, expressionIsOpAssignStatement);
      etrav.Traverse(expressionStatement.Expression);
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) Not Implemented</remarks>
    /// <param name="breakStatement"></param>
    public override void TraverseChildren(IBreakStatement breakStatement) {
      throw new TranslationException("Break statements are not handled");
      //StmtBuilder.Add(new Bpl.BreakCmd(breakStatement.Token(), "I dont know"));
    }

    public override void TraverseChildren(IContinueStatement continueStatement) {
      throw new TranslationException("Continue statements are not handled");
    }

    public override void TraverseChildren(ISwitchStatement switchStatement) {
      var eTraverser = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      eTraverser.Traverse(switchStatement.Expression);
      var conditionExpr = eTraverser.TranslatedExpressions.Pop();

      // Can't depend on default case existing or its index in the collection.
      var switchCases = new List<ISwitchCase>();
      ISwitchCase defaultCase = null;
      foreach (var switchCase in switchStatement.Cases) {
        if (switchCase.IsDefault) {
          defaultCase = switchCase;
        } else {
          switchCases.Add(switchCase);
        }
      }
      Bpl.StmtList defaultStmts = null;
      if (defaultCase != null) {
        var defaultBodyTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext);
        defaultBodyTraverser.Traverse(defaultCase.Body);
        defaultStmts = defaultBodyTraverser.StmtBuilder.Collect(defaultCase.Token());
      }

      Bpl.IfCmd ifCmd = null;

      for (int i = switchCases.Count-1; 0 <= i; i--) {

        var switchCase = switchCases[i];

        var scTraverser = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
        scTraverser.Traverse(switchCase.Expression);
        var scConditionExpr = scTraverser.TranslatedExpressions.Pop();
        var condition = Bpl.Expr.Eq(conditionExpr, scConditionExpr);

        var scBodyTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext);
        scBodyTraverser.Traverse(switchCase.Body);

        ifCmd = new Bpl.IfCmd(switchCase.Token(),
          condition,
          scBodyTraverser.StmtBuilder.Collect(switchCase.Token()),
          ifCmd,
          defaultStmts);
        defaultStmts = null; // default body goes only into the innermost if-then-else

      }
      StmtBuilder.Add(ifCmd);
    }

    /// <summary>
    /// If the local declaration has an initial value, then generate the
    /// statement "loc := e" from it. 
    /// Special case: if "loc" is a struct, then treat it as a call to 
    /// the default ctor.
    /// Otherwise ignore it.
    /// </summary>
    public override void TraverseChildren(ILocalDeclarationStatement localDeclarationStatement) {
      var initVal = localDeclarationStatement.InitialValue;
      var typ = localDeclarationStatement.LocalVariable.Type;
      var isStruct = TranslationHelper.IsStruct(typ);
      if (initVal == null && !isStruct)
        return;
      var boogieLocal = this.sink.FindOrCreateLocalVariable(localDeclarationStatement.LocalVariable);
      var boogieLocalExpr = Bpl.Expr.Ident(boogieLocal);
      var tok = localDeclarationStatement.Token();
      Bpl.Expr e = null;
      

      var structCopy = isStruct && initVal != null && !(initVal is IDefaultValue);
      // then a struct value of type S is being assigned: "lhs := s"
      // model this as the statement "call lhs := S..#copy_ctor(s)" that does the bit-wise copying
      if (isStruct) {
        if (!structCopy) {
          var defaultValue = new DefaultValue() {
            DefaultValueType = typ,
            Locations = new List<ILocation>(localDeclarationStatement.Locations),
            Type = typ,
          };
          var e2 = ExpressionFor(defaultValue);
          StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, boogieLocalExpr, e2));
        } else 
        /*if (structCopy) */{
          var proc = this.sink.FindOrCreateProcedureForStructCopy(typ);
          e = ExpressionFor(initVal);
          StmtBuilder.Add(new Bpl.CallCmd(tok, proc.Name, new List<Bpl.Expr> { e, }, new List<Bpl.IdentifierExpr>{ boogieLocalExpr, }));
        }
      } else {
        e = ExpressionFor(initVal);
        AddRecordCall(localDeclarationStatement.LocalVariable.Name.Value, initVal, e);
        StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, boogieLocalExpr, e));
      }
      return;
    }

    public override void TraverseChildren(IPushStatement pushStatement) {
      var tok = pushStatement.Token();
      var val = pushStatement.ValueToPush;
      var e = ExpressionFor(val);
      this.sink.operandStack.Push(e);
      return;
    }

    /// <summary>
    /// 
    /// </summary>
    public override void TraverseChildren(IReturnStatement returnStatement) {
      Bpl.IToken tok = returnStatement.Token();

      if (returnStatement.Expression != null) {
        ExpressionTraverser etrav = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
        etrav.Traverse(returnStatement.Expression);

        if (this.sink.ReturnVariable == null || etrav.TranslatedExpressions.Count < 1) {
          throw new TranslationException(String.Format("{0} returns a value that is not supported by the function", returnStatement.ToString()));
        }

        var returnExprBpl = etrav.TranslatedExpressions.Pop();
        AddRecordCall("<return value>", returnStatement.Expression, returnExprBpl);
        StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok,
            new Bpl.IdentifierExpr(tok, this.sink.ReturnVariable), returnExprBpl));
      }

      StmtBuilder.Add(new Bpl.ReturnCmd(returnStatement.Token()));
    }
    #endregion

    #region Goto and Labels

    public override void TraverseChildren(IGotoStatement gotoStatement) {
      IName target = gotoStatement.TargetStatement.Label;
      ITryCatchFinallyStatement targetStatement = this.sink.MostNestedTryStatement(target);
      int count = 0;
      while (count < this.sink.nestedTryCatchFinallyStatements.Count) {
        int index = this.sink.nestedTryCatchFinallyStatements.Count - count - 1;
        ITryCatchFinallyStatement nestedStatement = this.sink.nestedTryCatchFinallyStatements[index].Item1;
        if (targetStatement == nestedStatement)
          break;
        int labelId;
        string label;
        this.sink.AddEscapingEdge(nestedStatement, out labelId, out label);
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(labelId)));
        string finallyLabel = this.sink.FindOrCreateFinallyLabel(nestedStatement);
        StmtBuilder.Add(new Bpl.GotoCmd(gotoStatement.Token(), new List<string>(new string[] {finallyLabel})));
        StmtBuilder.AddLabelCmd(label);
        count++;
      }
      StmtBuilder.Add(new Bpl.GotoCmd(gotoStatement.Token(), new List<string>(new string[] {target.Value})));
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks> (mschaef) not sure if there is more work to do</remarks>
    /// <param name="labeledStatement"></param>
    public override void TraverseChildren(ILabeledStatement labeledStatement) {
      StmtBuilder.AddLabelCmd(labeledStatement.Label.Value);
      base.Traverse(labeledStatement.Statement);
    }

    #endregion

    #region Looping Statements

    public override void TraverseChildren(IWhileDoStatement whileDoStatement) {
      throw new TranslationException("WhileDo statements are not handled");
    }

    public override void TraverseChildren(IForEachStatement forEachStatement) {
      throw new TranslationException("ForEach statements are not handled");
    }

    public override void TraverseChildren(IForStatement forStatement) {
      throw new TranslationException("For statements are not handled");
    }

    public override void TraverseChildren(IDoUntilStatement doUntilStatement) {
      throw new TranslationException("DoUntil statements are not handled");
    }
    #endregion

    public void GenerateDispatchContinuation(ITryCatchFinallyStatement tryCatchFinallyStatement) {
      string continuationLabel = this.sink.FindOrCreateContinuationLabel(tryCatchFinallyStatement);
      Bpl.IfCmd elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, Bpl.Expr.Literal(true),
        TranslationHelper.BuildStmtList(new Bpl.GotoCmd(Bpl.Token.NoToken, new List<string>(new string[] {continuationLabel}))), null, null);
      List<string> edges = sink.EscapingEdges(tryCatchFinallyStatement);
      Bpl.IdentifierExpr labelExpr = Bpl.Expr.Ident(this.sink.LabelVariable);
      for (int i = 0; i < edges.Count; i++) {
        string label = edges[i];
        Bpl.GotoCmd gotoCmd = new Bpl.GotoCmd(Bpl.Token.NoToken, new List<string>(new string[] { label }));
        Bpl.Expr targetExpr = Bpl.Expr.Literal(i);
        elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, labelExpr, targetExpr),
          TranslationHelper.BuildStmtList(gotoCmd), elseIfCmd, null);
      }
      this.StmtBuilder.Add(elseIfCmd);
    }

    public void PropagateException() {
      int count = this.sink.nestedTryCatchFinallyStatements.Count;
      if (count == 0) {
        // Record every time an exception is propagated out of a method so it's
        // obvious that what is just a return to Boogie, and shows up in the
        // Corral trace as a return, is actually an exception propagation.
        AddRecordCall("<propagated exception>", sink.Heap.RefType, Bpl.Expr.Ident(sink.Heap.ExceptionVariable));
        StmtBuilder.Add(new Bpl.ReturnCmd(Bpl.Token.NoToken));
      }
      else {
        // Given that we already record C#-level throws and catches, recording
        // every time an exception is internally propagated to an outer try
        // block would be too distracting.
        Tuple<ITryCatchFinallyStatement, Sink.TryCatchFinallyContext> topOfStack = this.sink.nestedTryCatchFinallyStatements[count - 1];
        string exceptionTarget; 
        if (topOfStack.Item2 == Sink.TryCatchFinallyContext.InTry) {
          exceptionTarget = this.sink.FindOrCreateCatchLabel(topOfStack.Item1);
        }
        else if (topOfStack.Item2 == Sink.TryCatchFinallyContext.InCatch) {
          StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(-1)));
          exceptionTarget = this.sink.FindOrCreateFinallyLabel(topOfStack.Item1);
        }
        else {
          exceptionTarget = this.sink.FindOrCreateContinuationLabel(topOfStack.Item1);
        }
        StmtBuilder.Add(new Bpl.GotoCmd(Bpl.Token.NoToken, new List<string>(new string[] {exceptionTarget})));
      }
    }

    public void PropagateExceptionIfAny() {
      var cond = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.Heap.NullRef));
      var traverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext);
      traverser.PropagateException();
      Bpl.IfCmd ifCmd = new Bpl.IfCmd(Bpl.Token.NoToken, cond, traverser.StmtBuilder.Collect(Bpl.Token.NoToken), null, null);
      StmtBuilder.Add(ifCmd);
    }

    public override void TraverseChildren(ITryCatchFinallyStatement tryCatchFinallyStatement) {

      if (this.sink.Options.modelExceptions == 0) {
        this.Traverse(tryCatchFinallyStatement.TryBody);
        if (tryCatchFinallyStatement.FinallyBody != null)
          this.Traverse(tryCatchFinallyStatement.FinallyBody);
        return;
      }

      this.sink.nestedTryCatchFinallyStatements.Add(new Tuple<ITryCatchFinallyStatement, Sink.TryCatchFinallyContext>(tryCatchFinallyStatement, Sink.TryCatchFinallyContext.InTry));
      this.Traverse(tryCatchFinallyStatement.TryBody);
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(-1)));
      StmtBuilder.Add(new Bpl.GotoCmd(Bpl.Token.NoToken, new List<string>(new string[] {this.sink.FindOrCreateFinallyLabel(tryCatchFinallyStatement)})));
      this.sink.nestedTryCatchFinallyStatements.RemoveAt(this.sink.nestedTryCatchFinallyStatements.Count - 1);

      StmtBuilder.AddLabelCmd(this.sink.FindOrCreateCatchLabel(tryCatchFinallyStatement));
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LocalExcVariable), Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable)));
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.Heap.NullRef)));
      List<Bpl.StmtList> catchStatements = new List<Bpl.StmtList>();
      List<Bpl.Expr> typeReferences = new List<Bpl.Expr>();
      this.sink.nestedTryCatchFinallyStatements.Add(new Tuple<ITryCatchFinallyStatement, Sink.TryCatchFinallyContext>(tryCatchFinallyStatement, Sink.TryCatchFinallyContext.InCatch));
      foreach (ICatchClause catchClause in tryCatchFinallyStatement.CatchClauses) {
        typeReferences.Insert(0, this.sink.FindOrCreateTypeReference(catchClause.ExceptionType, true));
        StatementTraverser catchTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext);
        if (catchClause.ExceptionContainer != Dummy.LocalVariable) {
          Bpl.Variable catchClauseVariable = this.sink.FindOrCreateLocalVariable(catchClause.ExceptionContainer);
          var exceptionExpr = Bpl.Expr.Ident(this.sink.LocalExcVariable);
          catchTraverser.AddRecordCall(catchClause.ExceptionContainer.Name.Value, sink.Heap.RefType, exceptionExpr);
          catchTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(catchClauseVariable), exceptionExpr));
        }
        catchTraverser.Traverse(catchClause.Body);
        catchTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(-1)));
        catchTraverser.StmtBuilder.Add(new Bpl.GotoCmd(Bpl.Token.NoToken, new List<string>(new string[] {this.sink.FindOrCreateFinallyLabel(tryCatchFinallyStatement)})));
        catchStatements.Insert(0, catchTraverser.StmtBuilder.Collect(catchClause.Token()));
      }
      Bpl.IfCmd elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, Bpl.Expr.Literal(false), TranslationHelper.BuildStmtList(new Bpl.ReturnCmd(Bpl.Token.NoToken)), null, null);
      Bpl.Expr dynTypeOfOperand = this.sink.Heap.DynamicType(Bpl.Expr.Ident(this.sink.LocalExcVariable));
      for (int i = 0; i < catchStatements.Count; i++) {
        Bpl.Expr expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Subtype), new List<Bpl.Expr>(new Bpl.Expr[] {dynTypeOfOperand, typeReferences[i]}));
        elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, expr, catchStatements[i], elseIfCmd, null);
      }
      this.StmtBuilder.Add(elseIfCmd);
      this.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.LocalExcVariable)));
      PropagateException();
      this.sink.nestedTryCatchFinallyStatements.RemoveAt(this.sink.nestedTryCatchFinallyStatements.Count - 1);

      this.StmtBuilder.AddLabelCmd(this.sink.FindOrCreateFinallyLabel(tryCatchFinallyStatement));
      if (tryCatchFinallyStatement.FinallyBody != null) {
        this.sink.nestedTryCatchFinallyStatements.Add(new Tuple<ITryCatchFinallyStatement, Sink.TryCatchFinallyContext>(tryCatchFinallyStatement, Sink.TryCatchFinallyContext.InFinally));
        Bpl.Variable savedExcVariable = this.sink.CreateFreshLocal(this.sink.Heap.RefType);
        Bpl.Variable savedLabelVariable = this.sink.CreateFreshLocal(Bpl.Type.Int);
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(savedExcVariable), Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable)));
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(savedLabelVariable), Bpl.Expr.Ident(this.sink.LabelVariable)));
        this.Traverse(tryCatchFinallyStatement.FinallyBody);
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(savedExcVariable)));
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Ident(savedLabelVariable)));
        this.sink.nestedTryCatchFinallyStatements.RemoveAt(this.sink.nestedTryCatchFinallyStatements.Count - 1);
      }
      GenerateDispatchContinuation(tryCatchFinallyStatement);
      StmtBuilder.AddLabelCmd(this.sink.FindOrCreateContinuationLabel(tryCatchFinallyStatement));
      PropagateExceptionIfAny();
    }

    public override void TraverseChildren(IThrowStatement throwStatement) {
      if (this.sink.Options.modelExceptions == 0) {
        StmtBuilder.Add(new Bpl.AssumeCmd(throwStatement.Token(), Bpl.Expr.False));
        return;
      }
      ExpressionTraverser exceptionTraverser = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      exceptionTraverser.Traverse(throwStatement.Exception);
      var exceptionExpr = exceptionTraverser.TranslatedExpressions.Pop();
      AddRecordCall("<thrown exception>", throwStatement.Exception, exceptionExpr);
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), exceptionExpr));
      PropagateException();
    }

    public override void TraverseChildren(IRethrowStatement rethrowStatement) {
      var exceptionExpr = Bpl.Expr.Ident(this.sink.LocalExcVariable);
      AddRecordCall("<rethrown exception>", sink.Heap.RefType, exceptionExpr);
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), exceptionExpr));
      PropagateException();
    }

  }

}
