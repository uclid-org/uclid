/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2017.
 * Sanjit A. Seshia, Rohit Sinha and Pramod Subramanyan.
 *
 * All Rights Reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 1. Redistributions of source code must retain the above copyright notice,
 *
 * this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 *
 * documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from this
 * software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Author: Pramod Subramanyan
 *
 * SyGuS solver interface.
 *
 */

package uclid
package smt

import lang.{Identifier, Scope, Expr => langExpr}
import com.typesafe.scalalogging.Logger
import scala.collection.JavaConverters._
import scala.util.matching.Regex

import java.io.{File, PrintWriter}

object Constants {
  // Naming
  val InitFnName = "init-fn"
  val TransFnName = "trans-fn"
  val PostFnName = "post-fn"
  val InvFnName = "inv-fn"
  val SyGuSInstanceFileName = "uclid-sygus-instance"
  // Regex
  val SyGuSOutputInvFnRegex = "(?s)\\(define-fun " + InvFnName + " \\(.*\\).*Bool.*\\(.*\\)\\)"
  // Commands
  val SetLogicCmd = "(set-logic %s)"
  val CheckSynthCmd = "(check-synth)"
  // General SyGuS format commands
  val SyGuSDeclareFunCmd = "(declare-fun %1$s %2$s)"
  val SyGuSDeclareReadOnlyCmd = "(declare-var %1$s %2$s)"
  val SyGuSDeclareVarCmd = "(declare-var %1$s %2$s)\n(declare-var %1$s! %2$s)"
  val SyGuSSynthesizeFunCmd = "(synth-fun " + InvFnName + " %s Bool)"
  val InitConstraintCmd = "(constraint (=> (" + InitFnName + " %1$s) (" + InvFnName + " %1$s)))"
  val TransConstraintCmd = "(constraint (=> (and (" + InvFnName + " %1$s) (" + TransFnName + " %1$s %2$s)) (" + InvFnName + " %2$s)))"
  val PostConstraintCmd = "(constraint (=> (" + InvFnName + " %1$s) (" + PostFnName + " %1$s)))"
  // LoopInvGen format commands
  val LIGDeclareVarCmd = "(declare-primed-var %s %s)"
  val LIGSynthesizeInvCmd = "(synth-inv " + InvFnName + " %s)"
  val LIGInvConstraintsCmd = "(inv-constraint %s %s %s %s)".format(InvFnName, InitFnName, TransFnName, PostFnName)
}

class SyGuSInterface(args: List[String], dir : String) extends SMTLIB2Base with SynthesisContext {
  val sygusLog = Logger(classOf[SyGuSInterface])

  def getMutables(ctx : Scope) : List[(String, Type)] = {
    (ctx.map.map {
      p => {
        val namedExpr = p._2
        namedExpr match {
          case Scope.StateVar(_, _) | Scope.InputVar(_, _) | Scope.OutputVar(_, _) | Scope.SharedVar(_, _) =>
            Some((namedExpr.id.name, Converter.typeToSMT(namedExpr.typ)))
          case _ =>
            None
        }
      }
    }).toList.flatten
  }

  def getGlobals(ctx : Scope) : List[(String, Type)] = {
    (ctx.map.map {
      p => {
        val namedExpr = p._2
        namedExpr match {
          case Scope.Function(_, _) | Scope.ConstantVar(_, _) =>
            Some((namedExpr.id.name, Converter.typeToSMT(namedExpr.typ)))
          case _ =>
            None
        }
      }
    }).toList.flatten
  }

  override def getTypeName(suffix: String) : String = {
    counterId += 1
    "type_" + suffix + "_" + counterId.toString()
  }

  override def getVariableName(v : String) : String = {
    "var_" + v
    // v
  }

  def getPrimedVariableName(v : String) : String = {
    "var_" + v + "!"
    // v + "!"
  }

  def getEqExpr(ident : Identifier, expr : smt.Expr, ctx : Scope, prime : Boolean) : String = {
    val typ = Converter.typeToSMT(ctx.typeOf(ident).get)
    val symbol = Symbol(if (prime) ident.name + "!" else ident.name, typ)
    val eqExpr : smt.Expr = OperatorApplication(EqualityOp, List(symbol, expr))
    val symbols = Context.findSymbols(eqExpr)
    val symbolsP = symbols.filter(s => !variables.contains(s.id))
    symbolsP.foreach {
      (s) => {
        val sIdP = getVariableName(s.id)
        variables += (s.id -> Symbol(sIdP, s.symbolTyp))
      }
    }

    val trExpr = translateExpr(eqExpr, false)
    trExpr
  }

  def getDeclarations(readonly : List[(String, Type)], variable : List[(String, Type)]) : String = {
    val mutable = variable.map{ v => 
      {
        v._2 match {
          case MapType(inTypes, outType) =>
            throw new Utils.AssertionError("Can't mutate uninterpreted functions!")
          case _ => {
            val (typeName, otherDecls) = generateDatatype(v._2)
            Constants.SyGuSDeclareVarCmd.format(v._1, typeName)
            }
        }
      }}.toList
    val immutable = readonly.map{ v => 
      {
        v._2 match {
          case MapType(inTypes, outType) =>
            Constants.SyGuSDeclareFunCmd.format(v._1, 
            {
              "(" +
              inTypes.tail.fold(inTypes.head.toString){ (acc,i) => acc + " " + i.toString } +
              ") " + outType
            })
          // TODO Handle other globals
          case _ => {
            val (typeName, otherDecls) = generateDatatype(v._2)
            Constants.SyGuSDeclareReadOnlyCmd.format(v._1, typeName)
            }
        }
      }}.toList

    Utils.join(mutable++immutable, "\n")
  }
  
  def getStatePredicateTypeDecl(variables: List[(String, Type)]) : String = {
    "(" + Utils.join(variables.map(p => "(" + p._1 + " " + generateDatatype(p._2)._1 + ")"), " ") + ")" + " Bool"
  }

  def getTransRelationTypeDecl(variables: List[(String, Type)]) : String = {
    val vars = variables.map(p => "(" + p._1 + " " + generateDatatype(p._2)._1 + ")")
    val varsP = variables.map(p => "(" + p._1 + "! " + generateDatatype(p._2)._1 + ")")
    "(" + Utils.join(vars ++ varsP, " ") + ")" + " Bool"
  }
  
  def getSynthFunDecl(vars : List[(String, Type)], synthesizeFunCmd : String) : String = {
    val types = "(" + Utils.join(vars.map(p => "(" + p._1 + " " + generateDatatype(p._2)._1 + ")"), " ") + ")"
    synthesizeFunCmd.format(types)
  }

  def getInitFun(initExpr : Expr, vars : List[(String, Type)], ctx : Scope) : String = {
    // val symbols = Context.findSymbols(initExpr)
    // symbols.filter(p => !variables.contains(p.id)).foreach {
    //   (s) => {
    //     val idP = getVariableName(s.id)
    //     variables += (s.id -> (idP -> s.symbolTyp))
    //   }
    // }
    val funcBody = translateExpr(initExpr, false)
    val func = "(define-fun " + Constants.InitFnName + " " + getStatePredicateTypeDecl(vars) + " " + funcBody + ")"
    func
  }

  def getNextFun(nextExpr : Expr, vars : List[(String, Type)], ctx : Scope) : String = {
    // val symbols = Context.findSymbols(nextExpr)
    // symbols.filter(p => !variables.contains(p.id)).foreach {
    //   (s) => {
    //     val idP = getVariableName(s.id)
    //     variables += (s.id -> (idP -> s.symbolTyp))
    //   }
    // }
    val funcBody = translateExpr(nextExpr, false)
    val func = "(define-fun " + Constants.TransFnName + " " + getTransRelationTypeDecl(vars) + " " + funcBody + ")"
    func
  }

  def getPostFun(properties : List[Expr], variables : List[(String, Type)], ctx : Scope) : String = {
    val exprs = properties.map(p => translateExpr(p, false))
    val funBody = if (exprs.size == 1) exprs(0) else "(and %s)".format(Utils.join(exprs, " "))
    "(define-fun %s %s %s)".format(Constants.PostFnName, getStatePredicateTypeDecl(variables), funBody)
  }

  def getInitConstraint(variables : List[(String, Type)]) : String = {
    val args = Utils.join(variables.map(p => p._1), " ")
    Constants.InitConstraintCmd.format(args)
  }

  def getTransConstraint(variables : List[(String, Type)]) : String = {
    val args = Utils.join(variables.map(p => p._1), " ")
    val argsPrimed = Utils.join(variables.map(p => p._1 + "!"), " ")
    Constants.TransConstraintCmd.format(args, argsPrimed)
  }

  def getPostConstraint(variables : List[(String, Type)]) : String = {
    val args = Utils.join(variables.map(p => p._1), " ")
    Constants.PostConstraintCmd.format(args)
  }
  
  override def synthesizeInvariant(initExpr : Expr, initHavocs : List[(String, Type)], nextExpr: Expr, nextHavocs : List[(String, Type)], properties : List[smt.Expr], ctx : lang.Scope, logic : String) : Option[langExpr] = {
    var mutables = getMutables(ctx)
    Utils.assert(mutables.size > 0, "There are no variables in the given model.")
    sygusLog.debug("mutables: {}", mutables.toString())
    //TODO: Change state vars to all vars, since invariant synth doesn't allow for global variables.
    mutables = mutables.union(variables.filter(p => !p._1.endsWith("!")).map(p => p._2).toList).distinct
    sygusLog.debug("mutables: {}", mutables.toString())

    var globals = (getGlobals(ctx)++initHavocs++nextHavocs).distinct
    sygusLog.debug("globals: {}", globals.toString())

    val preamble = Constants.SetLogicCmd.format(logic)

    sygusLog.debug("initExpr: {}", initExpr.toString())
    val initFun = getInitFun(initExpr, mutables, ctx)
    sygusLog.debug("transFun: {}", nextExpr.toString())
    val transFun = getNextFun(nextExpr, mutables, ctx)
    sygusLog.debug("properties: {}", properties.toString())
    val postFun = getPostFun(properties, mutables, ctx)
      
    val instanceLines = {
      // General sygus format
      mutables = mutables.map(p => (getVariableName(p._1), p._2))
      val synthFunDecl = getSynthFunDecl(mutables, Constants.SyGuSSynthesizeFunCmd)
      val varDecls =  getDeclarations(globals, mutables)
      val initConstraint = getInitConstraint(mutables)
      val transConstraint = getTransConstraint(mutables)
      val postConstraint = getPostConstraint(mutables)
      val postamble = Constants.CheckSynthCmd
      List(preamble, synthFunDecl, varDecls, initFun, transFun, postFun, initConstraint, transConstraint, postConstraint, postamble)
    }

    val instance = "\n" + Utils.join(instanceLines, "\n")
    println("Printing instance of SyGuS problem")
    println(instance)
    sygusLog.debug(instance)
    val tmpFile = File.createTempFile(Constants.SyGuSInstanceFileName, ".sl")
    // tmpFile.deleteOnExit()
    new PrintWriter(tmpFile) {
      write(instance)
      close()
    }    
    val filename = tmpFile.getAbsolutePath()
    val cmdLine = (args ++ List(filename)).asJava
    sygusLog.debug("command line: {}", cmdLine.toString())
    val builder = new ProcessBuilder(cmdLine)
    if (dir.size > 0) {
      builder.directory(new File(dir))
    }
    builder.redirectErrorStream(true)
    val process = builder.start()
    val out = process.getInputStream()
    val in = process.getOutputStream()
    while (process.isAlive()) {}
    val numAvail = out.available()
    if (numAvail == 0) {
      Thread.sleep(5)
      return None
    } else {
      val bytes = Array.ofDim[Byte](numAvail)
      val numRead = out.read(bytes, 0, numAvail)
      val string = new String({
        if (numRead == numAvail) {
          bytes
        } else {
          bytes.slice(0, numRead)
        }
      })
      sygusLog.debug(string)
      // Find the invariant function
      val invFuncPattern = Constants.SyGuSOutputInvFnRegex.r
      val invString = (invFuncPattern findFirstIn string).mkString("").replaceAll("var_", "")
      // No invariant matches the regular expression invFuncPattern
      if (invString.length() == 0) return None
      // Found an invariant
      val fun = SExprParser.parseFunction(invString)
      // Convert to Uclid AST
      val funAST = fun match {
        case smt.DefineFun(id, args, body) =>
          smt.Converter.smtToExpr(body)
        case _ => throw new Utils.SyGuSParserError("Should not get here. Invariant function is not of DefineFun smt type.")
      }
      sygusLog.debug(fun.toString())
      sygusLog.debug(funAST.toString())
      return Some(funAST)
    }
  }
}
