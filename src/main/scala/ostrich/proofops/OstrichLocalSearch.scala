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
  //println("facts: ", goal.facts)
  val predConj     = facts.predConj
  //println("predConj: ", predConj)
  val concatLits   = predConj.positiveLitsWithPred(_str_++)
  println("concatLits: ", concatLits)
  val posRegularExpressions = predConj.positiveLitsWithPred(str_in_re_id)
  println("posRegularExpressions: ", posRegularExpressions)
  val negRegularExpressions = predConj.negativeLitsWithPred(str_in_re_id)
  //println("negRegularExpressions: ", negRegularExpressions)
  val concatPerRes = concatLits groupBy (_(2))
  println("concatPerRes: ", concatPerRes)
  val lengthLits   = predConj.positiveLitsWithPred(_str_len)
  val lengthMap    = (for (a <- lengthLits.iterator) yield (a(0), a(1))).toMap
  private val equalityPropagator = new OstrichEqualityPropagator(theory)


  val maxIterations = 100
  var i = 0

  def resolveConcat(t : LinearCombination)
  : Option[(LinearCombination, LinearCombination)] =
    for (lits <- concatPerRes get t) yield (lits.head(0), lits.head(1))

  def explore : Seq[Plugin.Action] = {
    val model = new MHashMap[Term, Either[IdealInt, Seq[Int]]]
    //println("model_start: ", model)

    //val auttest = fromString("7")
    //val wordtest = List(55)
    //val res = auttest.apply(wordtest)
    //println("TEST : ", res)

    //val auttest = fromString("")
    //println("TEST: ",auttest.apply(Vector()))


    val regexes    = new ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]
    val constructedRegexes = new ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]

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
    //println("Assignment: ", assignment)

    // transforms wordequations into regular expressions based on current assignment
    def wordEquationIntoRegex(assignment : MHashMap[Term, Option[String]]) : Unit = {
      constructedRegexes.clear()
      for (concat <- concatPerRes){
        for (element <- concat._2) {
          val we3 = element.tail.tail.head
          val we1 = element.head
          val we2 = element.tail.head

          val aut1 = assignment.get(we3) match {
            case Some(Some(x)) => fromString(x)
            case Some(None) => makeAnyString()
          }
          val str1 = assignment.get(we1) match {
            case Some(Some(x)) => x
            case Some(None) => ".*"
          }
          val str2 = assignment.get(we2) match {
            case Some(Some(x)) => x
            case Some(None) => ".*"
          }
          val aut2 = BricsAutomaton.apply(str1 + str2)
          val aut = aut1.&(aut2)
          val wordequation : (Term, Term, Term) = (we1, we2, we3)
          constructedRegexes += ((we3, aut, Some(wordequation)))
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
            regexes += ((a.head, aut, None))
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
        regexes += ((a.head, aut, None))
      }
      case `str_in_re_id` =>
        decodeRegexId(a, false)
    }
    for (a <- negRegularExpressions) a.pred match {
      case `str_in_re` => {
        val regex = regexExtractor regexAsTerm a(1)
        val aut = autDatabase.regex2ComplementedAutomaton(regex)
        regexes += ((a.head, aut, None))
      }
      case `str_in_re_id` =>
        decodeRegexId(a, true)
    }

    for (regex <- regexes){
      //println("regex: ", regex)
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
      for (regex <- regexes) {
        var word : Seq[Int] = Seq()
        assignment.get(regex._1) match {
          case Some(Some("")) => {
            if (!regex._2.apply(Vector())) {score += 1}
          }
          case Some(Some(x)) => for ( c <- x.toCharArray) {
            word = word :+ c.toInt
            if (!regex._2.apply(word)) {score += 1}
          }
          case _ => {
            score += 1
          }
        }
      }
      return score
    }

    def assignmentToModel(assignment : MHashMap[Term, Option[String]], model : MHashMap[Term, Either[IdealInt, Seq[Int]]]) :Unit = {
      for ((key, value) <- assignment) {
        var modelValue : Seq[Int] = Seq()
         value match {
           case Some("") => model.update(key, Right(Vector()))
           case Some(x) => for ( c <- x.toCharArray) {
             modelValue = modelValue :+ c.toInt
             model.update(key, Right(modelValue))
           }
         }
      }
    }

    def orderWordequations(assignment : MHashMap[Term, Option[String]], wordequations : ArrayBuffer[(Term, Term, Term)]) : ArrayBuffer[(Term, Term, Term)] = {
      def isAssigned(term: Term): Boolean = assignment.get(term).flatten.isDefined
      val (bothAssigned, others) = wordequations.partition { case (_, t2, t3) => isAssigned(t2) && isAssigned(t3) }
      val (oneAssigned, noneAssigned) = others.partition { case (_, t2, t3) => isAssigned(t2) || isAssigned(t3) }
      bothAssigned ++ oneAssigned ++ noneAssigned
    }

    // don't use this unassign method
    def unassignRandom(assignment: MHashMap[Term, Option[String]], tries : Int) : Unit = {
      if (tries == 0) {
        println("UNASSIGN FAILED")
        Seq()
      }
      val keyArray = assignment.keysIterator.toArray
      val keyIndex : Int = ThreadLocalRandom.current().nextInt(assignment.keySet.size)
      if ((!keyArray(keyIndex).isConstant) & assignment.get(keyArray(keyIndex)).flatten.isDefined){
        println("ASSIGNMENT UPDATED", assignment)
        return assignment.update(keyArray(keyIndex), None)
      }
      unassignRandom(assignment, tries-1)
    }

    def unassignRandomRelevant (assignment: MHashMap[Term, Option[String]], wordequations : ArrayBuffer[(Term, Term, Term)]) :Unit = {
      val candidates = new ArrayBuffer[Term]
      for (we <- wordequations) {
        if (!we._1.isConstant) {candidates += we._1}
        if (!we._2.isConstant) {candidates += we._2}
      }
      if (candidates.isEmpty) {println("UNASSIGN FAILED")}
      else {
        val keyIndex: Int = ThreadLocalRandom.current().nextInt(candidates.size)
        assignment.update(candidates(keyIndex), None)
      }
    }

    def constantStrVarResolveConflict (strVar :Term, usedRegexes : ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])], assignment : MHashMap[Term, Option[String]]) : MHashMap[Term, Option[String]] = {
      for (regex <- usedRegexes) {
        if (regex._1 == strVar && regex._2.isEmpty) {
          val unassignableTerms = new ArrayBuffer[(Term, Term, Term)]
          unassignableTerms += regex._3.getOrElse((strVar, strVar, strVar)) // Problem with None ??
          unassignRandomRelevant(assignment, unassignableTerms)
          wordEquationIntoRegex(assignment)
          val usedRegexes2 = regexes ++ constructedRegexes
          constantStrVarResolveConflict(strVar, usedRegexes2, assignment)
        }
      }
      return assignment
    }

    def makeStrVarIntersection(strVar : Term, regexes : ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]) : (Automaton, ArrayBuffer[(Term, Term, Term)]) = {
      var aut: Automaton = makeAnyString()
      val wordequation = new ArrayBuffer[(Term, Term, Term)]
      for (regex <- regexes) {
        if (regex._1 == strVar) {
          aut = aut.&(regex._2)
          regex._3 match {
            case Some(x) => wordequation += x
            case None => println("NONE ", regex._3)
          }
        }
      }
      return (aut, wordequation)
    }

    // TODO: regex assignment to wordequation assignment
    def regexAssignmentIntoWordequationAssignment(acceptedWord : Option[Seq[Int]], wordequations : ArrayBuffer[(Term, Term, Term)], assignment : MHashMap[Term, Option[String]]) : MHashMap[Term, Option[String]] = {
      var reorder = false
      val acceptedWordString = acceptedWord.map(_.map(_.toChar).mkString).getOrElse("") //should never be None
      val len = acceptedWordString.length
      val workingAssignment = assignment
      //println("Wordequations: ", wordequations)
      //println("workingAssignment 1: ", workingAssignment)
      breakable { for (we <- wordequations) {
        if (workingAssignment.get(we._3) == Some(None)){
          workingAssignment.update(we._3, Some(acceptedWordString))
        }
        (workingAssignment.get(we._1), workingAssignment.get(we._2)) match {
          case (Some(Some(x)),Some(Some(y))) => if (acceptedWordString != x+y) {
            // TODO: choose new word
             }
          case (Some(Some(x)), Some(None)) =>
            if (x.length > len) {
              // TODO: choose new word
            }
            else if (x == acceptedWordString.substring(0,x.length)) {
              workingAssignment.update(we._2, Some(acceptedWordString.substring(x.length)))
              reorder = true
              break
            }
            else {
              // TODO: choose new word
            }
          case (Some(None), Some(Some(x))) =>
            if (x.length > len) {
              // TODO: choose new word
            }
            else if (x == acceptedWordString.substring(len-x.length)) {
              workingAssignment.update(we._1, Some(acceptedWordString.substring(0,len-x.length)))
              reorder = true
              break
            }
            else {
              // TODO: choose new word
            }
          case (Some(None), Some(None)) =>
            val randomSplitIndex = ThreadLocalRandom.current().nextInt(acceptedWordString.length)
            workingAssignment.update(we._1, Some(acceptedWordString.substring(0,randomSplitIndex)))
            workingAssignment.update(we._2, Some(acceptedWordString.substring(randomSplitIndex)))
            reorder = true
            break
        }
      } }
      //println("workingAssignment: ", workingAssignment)
      if (reorder) {
        val newWordequations = orderWordequations(workingAssignment, wordequations)
        return regexAssignmentIntoWordequationAssignment(acceptedWord, newWordequations, workingAssignment)
      }
      return workingAssignment
    }

    //println("score: ", score(assignment))
    if (score(assignment) == 0) {
      println("SAT with following Assignment: ", assignment)
      assignmentToModel(assignment, model)
      println("MODEL: ", model)
      return equalityPropagator.handleSolution(goal, model.toMap)
    }

    // TODO: remove duplicate code fragment
    // TODO: forbidding strategy IMPORTANT!!!

    while (i < maxIterations) {
      println("Loop: " + i.toString)
      println("Assignment @ start of loop: ", assignment)
      wordEquationIntoRegex(assignment)
      //println("constructedRegexes: ", constructedRegexes)
      var usedRegexes = regexes ++ constructedRegexes
      //println("usedRegexes", usedRegexes)
      val choice = new MHashMap[MHashMap[Term, Option[String]], Int]
      //println("choice", choice)
      for (strVar <- assignment.keys) {
        //println("strVar: ", strVar)
        if (!strVar.isConstant) {
          //println("Non-constant strVra: ", strVar)
          var existsEmpty = false
          breakable {
            for (regex <- usedRegexes) {
              if (regex._1 == strVar && regex._2.isEmpty) {
                existsEmpty = true
                break
              }
            }
          }
          if (existsEmpty) {
            //println("existsEmpty strVar: ", strVar)
            var newAssignment = assignment
            newAssignment.update(strVar, None)
            //println("newAssignment", newAssignment)
            wordEquationIntoRegex(newAssignment)
            //println("constructedRegexes: ", constructedRegexes)
            usedRegexes = regexes ++ constructedRegexes
            //println("usedRegexes 2: ", usedRegexes)

            var strVarIntersection = makeStrVarIntersection(strVar, usedRegexes)
            //println("strVarIntersection: ", strVarIntersection)
            // TODO: UNSAT if all var unassigned and still empty
            var print = false //debug
            while (strVarIntersection._1.isEmpty) {
              print = true //debug
              // TODO: try different unassigning strategies here
              //unassignRandom(newAssignment, 500)
              unassignRandomRelevant(newAssignment, strVarIntersection._2)
              wordEquationIntoRegex(newAssignment)
              usedRegexes = regexes ++ constructedRegexes
              strVarIntersection = makeStrVarIntersection(strVar, usedRegexes)
              //println("UPDATE strVarIntersection", strVarIntersection._1)
            }
            //if (print) {println("UPDATE strVarIntersection", strVarIntersection._1)} //debug
            var strVarRegexAssignment = strVarIntersection._1.getAcceptedWord
            //strVarRegexAssignment = Some(Seq(120,121))
            //println("strVarRegexAssignment: ", strVarRegexAssignment)
            val orderedWordequations = orderWordequations(newAssignment, strVarIntersection._2)
            //println("newAssignment", newAssignment)
            //println("WordEquations: ", strVarIntersection._2)
            //println("Order Test: ", test)
            val strVarAssignment = regexAssignmentIntoWordequationAssignment(strVarRegexAssignment, orderedWordequations, newAssignment) //could probably just be newAssignment
            newAssignment = newAssignment ++ strVarAssignment
            val currentScore: Int = score(newAssignment)
            if (currentScore == 0) {
              println("SAT with following Assignment: ", newAssignment)
              assignmentToModel(newAssignment, model)
              println("MODEL: ", model)
              return equalityPropagator.handleSolution(goal, model.toMap)
            }
            choice.update(newAssignment, currentScore)
          }
        }
        else { //strVar is constant
          //println("Constant strVra: ", strVar)
          var newAssignment = assignment
          newAssignment = constantStrVarResolveConflict(strVar, usedRegexes, newAssignment)
          //println("Assignment after constant resolve conflict: ", newAssignment)

          var strVarIntersection = makeStrVarIntersection(strVar, usedRegexes)
          //println("strVarIntersection: ", strVarIntersection)
          // TODO: UNSAT if all var unassigned and still empty
          var print = false //debug
          while (strVarIntersection._1.isEmpty) {
            print = true //debug
            // TODO: try different unassigning strategies here
            //unassignRandom(newAssignment, 500)
            unassignRandomRelevant(newAssignment, strVarIntersection._2)
            wordEquationIntoRegex(newAssignment)
            usedRegexes = regexes ++ constructedRegexes
            strVarIntersection = makeStrVarIntersection(strVar, usedRegexes)
            //println("UPDATE strVarIntersection", strVarIntersection._1)
          }
          //if (print) {println("UPDATE strVarIntersection", strVarIntersection._1)} //debug
          var strVarRegexAssignment = strVarIntersection._1.getAcceptedWord
          //strVarRegexAssignment = Some(Seq(120,121))
          //println("strVarRegexAssignment: ", strVarRegexAssignment)
          val orderedWordequations = orderWordequations(newAssignment, strVarIntersection._2)
          //println("newAssignment", newAssignment)
          //println("WordEquations: ", strVarIntersection._2)
          //println("Order Test: ", test)
          val strVarAssignment = regexAssignmentIntoWordequationAssignment(strVarRegexAssignment, orderedWordequations, newAssignment) //could probably just be newAssignment
          newAssignment = newAssignment ++ strVarAssignment
          val currentScore: Int = score(newAssignment)
          if (currentScore == 0) {
            println("SAT with following Assignment: ", newAssignment)
            assignmentToModel(newAssignment, model)
            println("MODEL: ", model)
            return equalityPropagator.handleSolution(goal, model.toMap)
          }
          choice.update(newAssignment, currentScore)
        }
      }
      // choice should never be empty in final version ?
      if (choice.nonEmpty) {
        println("CHOICE: ", choice)
        val minValue = choice.values.min
        val minElements = choice.filter { case (_, value) => value == minValue }.toSeq
        val randomElement = minElements(ThreadLocalRandom.current().nextInt(minElements.length))
        assignment = randomElement._1
        //assignment = choice.minBy(_._2)._1
      }
      else {println("CHOICE EMPTY")}
      i += 1
    }
    println("maxIterations")

    Seq()
  }
}

