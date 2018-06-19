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

import lang.{Identifier, Scope}
import com.typesafe.scalalogging.Logger
import scala.collection.JavaConverters._
import scala.util.matching.Regex

import java.io.{File, PrintWriter}

class SyGuSInterface(args: List[String], dir : String, sygusFormat : Boolean) extends SMTLIB2Base with SynthesisContext {
  val sygusLog = Logger(classOf[SyGuSInterface])

  def getVariables(ctx : Scope) : List[(String, Type)] = {
    (ctx.map.map {
      p => {
        val namedExpr = p._2
        namedExpr match {
          case Scope.StateVar(_, _) | Scope.InputVar(_, _) |Scope.OutputVar(_, _) | Scope.SharedVar(_, _) | Scope.ConstantVar(_, _) =>
            Some((getVariableName(namedExpr.id.name), Converter.typeToSMT(namedExpr.typ)))
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
  }
  def getPrimedVariableName(v : String) : String = {
    "var_" + v + "!"
  }
  def getEqExpr(ident : Identifier, expr : smt.Expr, ctx : Scope, prime : Boolean) : String = {
    if (ctx.typeOf(ident) == None) return ""
    val typ = Converter.typeToSMT(ctx.typeOf(ident).get)
    val symbol = Symbol(if (prime) ident.name + "!" else ident.name, typ)
    val eqExpr : smt.Expr = OperatorApplication(EqualityOp, List(symbol, expr))
    val symbols = Context.findSymbols(eqExpr)
    val symbolsP = symbols.filter(s => !variables.contains(s.id))
    symbolsP.foreach {
      (s) => {
        val sIdP = getVariableName(s.id)
        variables += (s.id -> (sIdP, s.symbolTyp))
      }
    }

    val trExpr = translateExpr(eqExpr, false)
    trExpr
  }

  def getGeneralDeclarations(variables : List[(String, Type)]) : String = {
    val decls = variables.map{ v =>
      {
        val (typeName, otherDecls) = generateDatatype(v._2)
        Utils.assert(otherDecls.size == 0, "Datatype declarations are not supported yet.")
        // FIXME: to handle otherDecls
        "(declare-var %1$s %2$s)\n(declare-var %1$s! %2$s)".format(v._1, typeName)
      }
    }
    Utils.join(decls, "\n")
  }

  def getPrimedDeclarations(variables : List[(String, Type)]) : String = {
    val decls = variables.map{ v =>
      {
        val (typeName, otherDecls) = generateDatatype(v._2)
        Utils.assert(otherDecls.size == 0, "Datatype declarations are not supported yet.")
        // FIXME: to handle otherDecls
        "(declare-primed-var %s %s)".format(v._1, typeName)
      }
    }
    Utils.join(decls, "\n")
  }
  
  def getStatePredicateTypeDecl(variables: List[(String, Type)]) : String = {
    "(" + Utils.join(variables.map(p => "(" + p._1 + " " + generateDatatype(p._2)._1 + ")"), " ") + ")" + " Bool"
  }

  def getTransRelationTypeDecl(variables: List[(String, Type)]) : String = {
    val vars = variables.map(p => "(" + p._1 + " " + generateDatatype(p._2)._1 + ")")
    val varsP = variables.map(p => "(" + p._1 + "! " + generateDatatype(p._2)._1 + ")")
    "(" + Utils.join(vars ++ varsP, " ") + ")" + " Bool"
  }
  
  def getSynthFunDecl(vars : List[(String, Type)]) : String = {
    val types = "(" + Utils.join(vars.map(p => "(" + p._1 + " " + generateDatatype(p._2)._1 + ")"), " ") + ")"
    "(synth-fun inv-f %s Bool)".format(types)
  }

  def getSynthInvDecl(vars : List[(String, Type)]) : String = {
    val types = "(" + Utils.join(vars.map(p => "(" + p._1 + " " + generateDatatype(p._2)._1 + ")"), " ") + ")"
    "(synth-inv inv-f %s)".format(types)
  }

  def getInitFun(initState : Map[Identifier, Expr], variables : List[(String, Type)], ctx : Scope) : String = {
    val initExprs = initState.map(p => getEqExpr(p._1, p._2, ctx, false)).toList
    val funcBody = "(and " + Utils.join(initExprs, " ") + ")"
    val func = "(define-fun init-fn " + getStatePredicateTypeDecl(variables) + " " + funcBody + ")"
    func
  }

  def getNextFun(nextState : Map[Identifier, Expr], variables : List[(String, Type)], ctx : Scope) : String = {
    // FIXME: some variables are not primed. Why?
    val nextExprs = nextState.map(p => getEqExpr(p._1, p._2, ctx, true)).toList
    val funcBody = "(and " + Utils.join(nextExprs, " ") + ")"
    val func = "(define-fun trans-fn " + getTransRelationTypeDecl(variables) + " " + funcBody + ")"
    func
  }

  def getPostFun(properties : List[Expr], variables : List[(String, Type)], ctx : Scope) : String = {
    val exprs = properties.map(p => translateExpr(p, false))
    val funBody = if (exprs.size == 1) exprs(0) else "(and %s)".format(Utils.join(exprs, " "))
    "(define-fun post-fn %s %s)".format(getStatePredicateTypeDecl(variables), funBody)
  }

  def getInitConstraint(variables : List[(String, Type)]) : String = {
    val args = Utils.join(variables.map(p => p._1), " ")
    "(constraint (=> (init-fn %1$s) (inv-f %1$s)))".format(args)
  }

  def getTransConstraint(variables : List[(String, Type)]) : String = {
    val args = Utils.join(variables.map(p => p._1), " ")
    val argsPrimed = Utils.join(variables.map(p => p._1 + "!"), " ")
    "(constraint (=> (and (inv-f %1$s) (trans-fn %1$s %2$s)) (inv-f %2$s)))".format(args, argsPrimed)
  }

  def getPostConstraint(variables : List[(String, Type)]) : String = {
    val args = Utils.join(variables.map(p => p._1), " ")
    "(constraint (=> (inv-f %1$s) (post-fn %1$s)))".format(args)
  }
  
  override def synthesizeInvariant(initState : Map[Identifier, Expr], nextState: Map[Identifier, Expr], properties : List[smt.Expr], ctx : Scope) : Option[smt.Expr] = {
    val variables = getVariables(ctx)
    val preamble = "(set-logic LIA)" // FIXME: need to identify logics
    val initFun = getInitFun(initState, variables, ctx)
    val transFun = getNextFun(nextState, variables, ctx)
    val postFun = getPostFun(properties, variables, ctx)
    
    val instanceLines = if (sygusFormat) {
      // General sygus format
      val synthFunDecl = getSynthFunDecl(variables)
      val varDecls = getGeneralDeclarations(variables)
      val initConstraint = getInitConstraint(variables)
      val transConstraint = getTransConstraint(variables)
      val postConstraint = getPostConstraint(variables)
      val postamble = "(check-synth)"
      List(preamble, synthFunDecl, varDecls, initFun, transFun, postFun, initConstraint, transConstraint, postConstraint, postamble)
    } else {
      // Loop invariant format
      val synthInvDecl = getSynthInvDecl(variables)
      val varDecls = getPrimedDeclarations(variables)
      val postamble = "(inv-constraint inv-fn init-fn trans-fn post-fn)\n\n(check-synth)"
      List(preamble, synthInvDecl, varDecls, initFun, transFun, postFun, postamble)
    }
    val instance = "\n" + Utils.join(instanceLines, "\n")
    sygusLog.debug(instance)
    val tmpFile = File.createTempFile("uclid-sygus-instance", ".sl")
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
      val invFuncPattern = "(?s)\\(define-fun inv-f \\(.*\\).*Bool.*\\(.*\\)\\)".r
      val invString = (invFuncPattern findFirstIn string).mkString("")
      // No invariant matches the regular expression invFuncPattern
      if (invString.length() == 0) return None
      // Found an invariant
      val fun = SExprParser.parseFunction(invString)
      sygusLog.debug(fun.toString())
      return Some(fun)
    }
  }

}