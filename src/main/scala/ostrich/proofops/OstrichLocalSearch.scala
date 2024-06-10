/**
 * This file is part of Ostrich, an SMT solver for strings.
 * Copyright (c) 2022 Oliver Markgraf, Philipp Ruemmer. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package ostrich.proofops

import ap.basetypes.IdealInt
import ap.interpolants.StructuredPrograms.Assignment
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import ap.terfor.{TerForConvenience, Term}
import ostrich._
import ostrich.automata.BricsAutomaton.{fromString, makeAnyString, prefixAutomaton, suffixAutomaton}
import ostrich.automata.{AutomataUtils, Automaton, BricsAutomaton}

import java.util.Collections
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.{HashMap => MHashMap}
import scala.concurrent.forkjoin.ThreadLocalRandom
import scala.util.control.Breaks.{break, breakable}

class OstrichLocalSearch(goal : Goal,
                         theory : OstrichStringTheory,
                         flags : OFlags)  {
  import TerForConvenience._
  import theory.{FunPred, StringSort, _str_++, str_in_re, str_in_re_id, autDatabase, _str_len, int_to_str, strDatabase, str_prefixof, str_replace, str_suffixof, str_to_int}

  implicit val order = goal.order


  val facts        = goal.facts
  println("facts: ", goal.facts)
  val predConj     = facts.predConj
  println("predConj: ", predConj)
  val concatLits   = predConj.positiveLitsWithPred(_str_++)
  println("concatLits: ", concatLits)
  val posRegularExpressions = predConj.positiveLitsWithPred(str_in_re_id)
  println("posRegularExpressions: ", posRegularExpressions)
  val negRegularExpressions = predConj.negativeLitsWithPred(str_in_re_id)
  println("negRegularExpressions: ", negRegularExpressions)
  val concatPerRes = concatLits groupBy (_(2))
  println("concatPerRes: ", concatPerRes)
  val lengthLits   = predConj.positiveLitsWithPred(_str_len)
  val lengthMap    = (for (a <- lengthLits.iterator) yield (a(0), a(1))).toMap
  private val equalityPropagator = new OstrichEqualityPropagator(theory)


  val maxIterations = 10000
  var i = 0

  def resolveConcat(t : LinearCombination)
  : Option[(LinearCombination, LinearCombination)] =
    for (lits <- concatPerRes get t) yield (lits.head(0), lits.head(1))

  def explore : Seq[Plugin.Action] = {
    val model = new MHashMap[Term, Either[IdealInt, Seq[Int]]]
    println("model_start: ", model)

    val regexes    = new ArrayBuffer[(Term, Automaton)]
    val constructedRegexes = new ArrayBuffer[(Term, Automaton)]

    // initial assignment
    // sets all non constant variables to empty string
    // TODO: try different initial assignments
    var assignment = new MHashMap[Term, Option[String]]
    for (concat <- concatPerRes) {
      for (element <- concat._2) {
        assignment.update(element.tail.tail.head, Some(strDatabase.term2Str(element.tail.tail.head).getOrElse("")))
        assignment.update(element.tail.head, Some(strDatabase.term2Str(element.tail.head).getOrElse("")))
        assignment.update(element.head, Some(strDatabase.term2Str(element.head).getOrElse("")))
      }
    }
    for (regex <- posRegularExpressions) {
      assignment.update(regex.head, Some(strDatabase.term2Str(regex.head).getOrElse("")))
    }
    for (regex <- negRegularExpressions) {
      assignment.update(regex.head, Some(strDatabase.term2Str(regex.head).getOrElse("")))
    }
    println("Assignment: ", assignment)

    // transforms wordequations into regular expressions based on current assignment
    def wordEquationIntoRegex(assignment : MHashMap[Term, Option[String]]) : Unit = {
      constructedRegexes.clear()
      for (concat <- concatPerRes){
        for (element <- concat._2) {
          val aut1 = assignment.get(element.tail.tail.head) match {
            case Some(Some(x)) => fromString(x)
            case Some(None) => makeAnyString()
          }
          val str1 = assignment.get(element.head) match {
            case Some(Some(x)) => x
            case Some(None) => ".*"
          }
          val str2 = assignment.get(element.tail.head) match {
            case Some(Some(x)) => x
            case Some(None) => ".*"
          }
          val aut2 = BricsAutomaton.apply(str1 + str2)
          val aut = aut1.&(aut2)
          constructedRegexes += ((element.tail.tail.head,aut))
        }
      }
    }

    def decodeRegexId(a : Atom, complemented : Boolean) : Unit = a(1) match {
      case LinearCombination.Constant(id) => {
        val autOption =
          if (complemented)
            autDatabase.id2ComplementedAutomaton(id.intValueSafe)
          else
            autDatabase.id2Automaton(id.intValueSafe)

        autOption match {
          case Some(aut) =>
            regexes += ((a.head, aut))
          case None =>
            throw new Exception ("Could not decode regex id " + a(1))
        }
      }
      case lc =>
        throw new Exception ("Could not decode regex id " + lc)
    }

    val regexExtractor =
      theory.RegexExtractor(goal)

    for (a <- posRegularExpressions) a.pred match {
      case `str_in_re` => {
        val regex = regexExtractor regexAsTerm a(1)
        val aut = autDatabase.regex2Automaton(regex)
        regexes += ((a.head, aut))
      }
      case `str_in_re_id` =>
        decodeRegexId(a, false)
    }
    for (a <- negRegularExpressions) a.pred match {
      case `str_in_re` => {
        val regex = regexExtractor regexAsTerm a(1)
        val aut = autDatabase.regex2ComplementedAutomaton(regex)
        regexes += ((a.head, aut))
      }
      case `str_in_re_id` =>
        decodeRegexId(a, true)
    }

    for (regex <- regexes){
      println("regex: ", regex)
      val acceptedWord = regex._2.getAcceptedWord
      //println("acceptedWord: ", acceptedWord)
      val isAccepted = regex._2.apply(acceptedWord.get)
      //println("isAccepted: ", isAccepted)
      val product = AutomataUtils.product(Seq(regex._2))
      val concat = AutomataUtils.concat(regex._2.asInstanceOf[BricsAutomaton], regex._2.asInstanceOf[BricsAutomaton])
      model.put(regex._1, Right(acceptedWord.get))
      //println("aw class", acceptedWord.get.getClass)
    }


    // scoring, solution if score == 0
    def score(assignment: MHashMap[Term, Option[String]]) : Int = {
      var score = 0
      for (concat <- concatPerRes) {
        for (element <- concat._2) {
           (assignment.get(element.tail.tail.head), assignment.get(element.head), assignment.get(element.tail.head)) match {
             case (Some(Some(x)),Some(Some(y)),Some(Some(z))) => if (x != y + z){score += 1}
             case _ => score += 1
          }
        }
      }
      // TODO: str to Seq[Int] needs fixing
      for (regex <- regexes) {
        var word : Seq[Int] = Seq()
        assignment.get(regex._1) match {
          case Some(Some(x)) => for ( c <- x.toCharArray) {
            word = word :+ c.toInt
            if (!regex._2.apply(word)) {score += 1}
          }
          case _ => score += 1
        }
      }
      return score
    }

    // TODO: only choose between assigned strVar
    def unassignRandom(assignment: MHashMap[Term, Option[String]]) : Unit = {
      val keyArray = assignment.keysIterator.toArray
      var keyIndex : Int = ThreadLocalRandom.current().nextInt(assignment.keySet.size)
      assignment.update(keyArray(keyIndex), None)
    }

    def makeStrVarIntersection(strVar : Term, regexes : ArrayBuffer[(Term,Automaton)]) : Automaton = {
      val aut = makeAnyString()
      for (regex <- regexes) {
        if (regex._1 == strVar) {
          aut.&(regex._2)
        }
      }
      return aut
    }

    //println("assignment", assignment)
    //unassignRandom(assignment)
    //println("assignment", assignment)

    // TODO: regex assignment to wordequation assignment
    def regexAssignmentIntoWordequationAssignment(acceptedWord : Option[Seq[Int]]) : MHashMap[Term, Option[String]] = {
      //should never be None
      var acceptedWordString = acceptedWord.map(_.map(_.toChar).mkString).getOrElse("")
      //placeholder
      return new MHashMap[Term, Option[String]]()
    }

    if (score(assignment) == 0) {
      // TODO: assignment to model
      println("SAT with following Assignment: ", assignment)
      return equalityPropagator.handleSolution(goal, model.toMap)
    }


    while (i < maxIterations) {
      wordEquationIntoRegex(assignment)
      println("constructedRegexes: ", constructedRegexes)
      var usedRegexes = regexes ++ constructedRegexes
      println("usedRegexes", usedRegexes)
      val choice = new MHashMap[MHashMap[Term, Option[String]], Int]
      println("choice", choice)
      for (strVar <- assignment.keys) {
        var existsEmpty = false
        breakable { for (regex <- usedRegexes) {
          if (regex._1 == strVar && regex._2.isEmpty) {
            existsEmpty = true
            break
          }
        } }
        if (existsEmpty) {
          var newAssignment = assignment
          newAssignment.update(strVar, None)
          println("newAssignment", newAssignment)
          wordEquationIntoRegex(newAssignment)
          usedRegexes = regexes ++ constructedRegexes
          println("usedRegexes 2: ", usedRegexes)
          var strVarIntersection = makeStrVarIntersection(strVar, usedRegexes)
          // TODO: UNSAT if all var unassigned and still empty
          while (strVarIntersection.isEmpty) {
            // TODO: try different unassigning strategies here
            unassignRandom(newAssignment)
            wordEquationIntoRegex(newAssignment)
            usedRegexes = regexes ++ constructedRegexes
            strVarIntersection = makeStrVarIntersection(strVar, usedRegexes)
          }
          var strVarRegexAssignment = strVarIntersection.getAcceptedWord
          var strVarAssignment = regexAssignmentIntoWordequationAssignment(strVarRegexAssignment)
          newAssignment = newAssignment ++ strVarAssignment
          var currentScore: Int = score(newAssignment)
          if (currentScore == 0) {
            // TODO: assignment to model
            println("SAT with following Assignment: ", assignment)
            return equalityPropagator.handleSolution(goal, model.toMap)
          }
          choice.update(newAssignment, currentScore)
        }
      }
      // choice should never be empty in final version ?
      if (choice.nonEmpty) {
        assignment = choice.minBy(_._2)._1
      }
      i += 1
    }
    println("maxIterations")

    Seq()
  }
}

