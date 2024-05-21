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
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import ap.terfor.{TerForConvenience, Term}
import ostrich._
import ostrich.automata.{AutomataUtils, Automaton, BricsAutomaton}

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.{HashMap => MHashMap}

class OstrichLocalSearch(goal : Goal,
                         theory : OstrichStringTheory,
                         flags : OFlags)  {
  import TerForConvenience._
  import theory.{FunPred, StringSort, _str_++, str_in_re, str_in_re_id, autDatabase, _str_len, int_to_str, strDatabase, str_prefixof, str_replace, str_suffixof, str_to_int}

  implicit val order = goal.order

  val facts        = goal.facts
  //println("facts: ", goal.facts)
  val predConj     = facts.predConj
  //println("predConj: ", predConj)
  val concatLits   = predConj.positiveLitsWithPred(_str_++)
  //println("concatLits: ", concatLits)
  val posRegularExpressions = predConj.positiveLitsWithPred(str_in_re_id)
  //println("posRegularExpressions: ", posRegularExpressions)
  val negRegularExpressions = predConj.negativeLitsWithPred(str_in_re_id)
  //println("negRegularExpressions: ", negRegularExpressions)
  val concatPerRes = concatLits groupBy (_(2))
  //println("concatPerRes: ", concatPerRes)
  val lengthLits   = predConj.positiveLitsWithPred(_str_len)
  val lengthMap    = (for (a <- lengthLits.iterator) yield (a(0), a(1))).toMap
  private val equalityPropagator = new OstrichEqualityPropagator(theory)

  var score = 0 // #falsified clauses
  var bestScore: Int = java.lang.Integer.MAX_VALUE

  def resolveConcat(t : LinearCombination)
  : Option[(LinearCombination, LinearCombination)] =
    for (lits <- concatPerRes get t) yield (lits.head(0), lits.head(1))

  def explore : Seq[Plugin.Action] = {
    val model = new MHashMap[Term, Either[IdealInt, Seq[Int]]]
    println("model_start: ", model)

    // TODO: Assign initial values
    // TODO: Finish WE into RegEx transformation
    // TODO: Loop:
    //  heuristic to choose which RegEx to satisfy in this iteration (most restrictive first ?)
    //  find RegEX solution
    //  convert RegEX solution back to WE solution (if applicable)
    //  assign values accordingly
    // check solution

    val regexes    = new ArrayBuffer[(Term, Automaton)]

    // transforming WE into RegEx

    for (concat <- concatPerRes) {
      for ((element) <- concat._2) {

        //println(concat._1.isConstant)
        val regExPart1 = if (element.tail.tail.head.isConstant) {
          // TODO: transform back to string value
          "(str.to_re \"" + element.tail.tail.head.toString() + "\")"
        } else {
          "(re.all)"
        }

        val regExPart2 = if (element.head.isConstant) {
          // TODO: transform back to string value
          "(str.to_re \"" + element.head.toString() + "\")"
        } else {
          "(re.all)"
        }

        val regExPart3 = if (element.tail.head.isConstant) {
          // TODO: transform back to string value
          "(str.to_re \"" + element.tail.head.toString() + "\")"
        } else {
          "(re.all)"
        }
        val regEx = "(re.union " + regExPart1 + " (re.++ " + regExPart2 + " " + regExPart3 + "))"
        println("regEx: ", regEx)
        // TODO: actually do something with new RegEx
        //posRegularExpressions = posRegularExpressions :+ (new Atom())
        //println("posRegularExpressions modified:", posRegularExpressions)
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


    // checking Solution
    var foundSolution = false
    score = 0

    println("model: ", model)
    //for (a <- model){
      //println("test: ", a._1, a._2)
    //}

    for (concat <- concatPerRes){
      //println("concat: ", concat)
      //println("concat 1: ", concat._1)
      //println("concat 2: ", concat._2.head.head)
      //println("concat 3: ", concat._2.head.tail.head)
      //println("concat 1 class: ", concat._1.getClass)
      //println("concat 2 class: ", concat._2.head.head.getClass)
      //println("concat 3 class: ", concat._2.head.tail.head.getClass)

      var v1: Option[Either[IdealInt, Seq[Int]]] = None //left side
      var v2: Option[Either[IdealInt, Seq[Int]]] = None //right side
      var v3: Option[Either[IdealInt, Seq[Int]]] = None // right side

      for ((element) <- concat._2) {
        //get the assigned values

        //println("element: ", element)
        v1 = model.get(element.tail.tail.head)
        //println("v1 : ", v1)
        //println(element.tail.tail.head)
        v2 = model.get(element.head)
        //println("v2 : ", v2)
        //println(element.head)
        v3 = model.get(element.tail.head)
        //println("v3 : ", v3)
        //println(element.tail.head)

        println("v: ", v1, v2, v3)
        //println("v classes: ", v1.getClass, v2.getClass, v3.getClass)

        //concat right side
        val v23 = for {
          Right(vec2) <- v2
          Right(vec3) <- v3
        } yield vec2 ++ vec3
        //println("v23: ", v23)

        //check equality left and right side
        val result = for {
          Right(vec1) <- v1
          combinedVec <- v23
        } yield vec1 == combinedVec

        //scoring
        result match {
          case Some(false) => score += 1
          case Some(true) => println("we sat")
          case None => score += 1
        }
      }


    }

    for (regex <- regexes) {
      //get the assigned values
      val variable = model.get(regex._1)
      val strVariable: Seq[Int] = variable match{
        case Some(Right(strVariable)) => strVariable
        case _ => Seq.empty[Int]
      }
      //check if assignment is satisfying
      val result = regex._2.apply(strVariable)
      //scoring
      if (!result) {
        score += 1
      }
      else {
        println("regex sat")
      }
    }

    //println("goal: ", goal)

    if (score <= bestScore){
      bestScore = score
      // TODO: only update assignment if new best score
    }
    if (score == 0) {
      foundSolution = true
    }
    else {
      // TODO: search for new solution
    }

    if (foundSolution){
      equalityPropagator.handleSolution(goal, model.toMap)
    }
    else{
      Seq()
    }
  }

}

/*
while not solution:
  assign solution
  check solution
 */
