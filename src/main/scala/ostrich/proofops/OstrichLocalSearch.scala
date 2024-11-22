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
import ap.proof.theoryPlugins.Plugin.GoalState
import ap.terfor.conjunctions.Conjunction
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
import scala.collection.immutable.Queue
import ostrich.OstrichStringTheory


class OstrichLocalSearch(goal : Goal,
                         theory : OstrichStringTheory,
                         flags : OFlags)  {
  import TerForConvenience._
  import theory.{FunPred, StringSort, _str_++, str_in_re, str_in_re_id, autDatabase, _str_len, int_to_str, strDatabase, str_prefixof, str_replace, str_suffixof, str_to_int}

  implicit val order = goal.order

  val facts        = goal.facts
  val predConj     = facts.predConj
  val concatLits   = predConj.positiveLitsWithPred(_str_++)
  val posRegularExpressions = predConj.positiveLitsWithPred(str_in_re_id)
  val negRegularExpressions = predConj.negativeLitsWithPred(str_in_re_id)
  val concatPerRes = concatLits groupBy (_(2))
  val replacesLits = predConj.positiveLitsWithPred(FunPred(str_replace))
  val lengthLits   = predConj.positiveLitsWithPred(_str_len)
  val lengthMap    = (for (a <- lengthLits.iterator) yield (a(0), a(1))).toMap
  private val equalityPropagator = new OstrichEqualityPropagator(theory)

  val maxIterations = 5000
  var i = 0
  val maxQueueSize = 20 //max iterations with same score
  val tabooSize = 2 //amount of previous assignments that are not allowed as current assignment
  var result =(goal, new mutable.HashMap[Term, Either[IdealInt, Seq[Int]]].toMap) :(Goal, Map[Term, Either[IdealInt, Seq[Int]]])

  class FixedSizeQueue[A](val maxSize: Int) {
    private var queue = Queue.empty[A]

    def enqueue(elem: A): Unit = {
      if (queue.size >= maxSize) {
        queue = queue.dequeue._2 // remove the oldest element
      }
      queue = queue.enqueue(elem)
    }

    def dequeue(): (A, FixedSizeQueue[A]) = {
      val (elem, newQueue) = queue.dequeue
      (elem, new FixedSizeQueue[A](maxSize) {
        queue = newQueue
      })
    }

    def contains(elem: A): Boolean = {
      queue.contains(elem)
    }

    def toList: List[A] = queue.toList

    def size: Int = queue.size

    def allSame: Boolean = {
      if (queue.isEmpty) true // If the queue is empty, we consider all elements to be the same
      else {
        val first = queue.head
        queue.forall(_ == first)
      }
    }

    override def toString: String = queue.mkString("FixedSizeQueue(", ", ", ")")
  }

  def resolveConcat(t : LinearCombination)
  : Option[(LinearCombination, LinearCombination)] =
    for (lits <- concatPerRes get t) yield (lits.head(0), lits.head(1))

  def explore : Seq[Plugin.Action] = {
    val model = new MHashMap[Term, Either[IdealInt, Seq[Int]]]

    val regexes    = new ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]
    var constructedRegexesWordequations = new ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]
    //var constructedRegexesReplace = new ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]

    // initial assignment
    // sets all non constant variables to empty string
    var assignment = new MHashMap[Term, Option[String]]

    def initialAssignmentAllEmpty(assignment: MHashMap[Term, Option[String]]) : MHashMap[Term, Option[String]] = {
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
      for (replace <- replacesLits) {
        assignment.update(replace.tail.tail.tail.head, Some(strDatabase.term2Str(replace.tail.tail.head).getOrElse("")))
        assignment.update(replace.tail.tail.head, Some(strDatabase.term2Str(replace.tail.tail.head).getOrElse("")))
        assignment.update(replace.tail.head, Some(strDatabase.term2Str(replace.tail.head).getOrElse("")))
        assignment.update(replace.head, Some(strDatabase.term2Str(replace.head).getOrElse("")))
      }
      return assignment
    }

    def initialAssignment2(assignment: MHashMap[Term, Option[String]]) : MHashMap[Term, Option[String]] = {
      for (concat <- concatPerRes) {
        for (element <- concat._2) {
          assignment.update(element.tail.tail.head, Some(strDatabase.term2Str(element.tail.tail.head).getOrElse("")))
          assignment.update(element.tail.head, Some(strDatabase.term2Str(element.tail.head).getOrElse("")))
          assignment.update(element.head, Some(strDatabase.term2Str(element.head).getOrElse("")))
        }
      }
      for (replace <- replacesLits) {
        assignment.update(replace.tail.tail.tail.head, Some(strDatabase.term2Str(replace.tail.tail.head).getOrElse("")))
        assignment.update(replace.tail.tail.head, Some(strDatabase.term2Str(replace.tail.tail.head).getOrElse("")))
        assignment.update(replace.tail.head, Some(strDatabase.term2Str(replace.tail.head).getOrElse("")))
        assignment.update(replace.head, Some(strDatabase.term2Str(replace.head).getOrElse("")))
      }
      for (regex <- regexes) {
        val aw = regex._2.getAcceptedWord.getOrElse(Seq())
        val awSeqStr = for (c <- aw.toIndexedSeq) yield c.toChar.toString
        val awStr = awSeqStr.mkString("")
        assignment.update(regex._1, Some(strDatabase.term2Str(regex._1).getOrElse(awStr)))
      }
      return assignment
    }


    def complexity() : MHashMap[Term, Int] = {
      val complexityMap = new MHashMap[Term, Int]
      def getComplexity(term: Term) : Int = {
        if (complexityMap.contains(term)) {return complexityMap(term)}
        val vectors = concatPerRes.getOrElse(term, List())
        val complexity = vectors.flatMap { vector =>
          vector.filter(_ != term).collect {
            case t if concatPerRes.contains(t) => getComplexity(t)
            case t if t.isConstant => 0
            case _ => 1
          }
        }.sum

        complexityMap(term) = complexity
        return complexity
      }
      concatPerRes.keys.foreach(getComplexity)
      return complexityMap
    }

    val complexityMap = complexity()

    // initial assignment based on parts of strVars
    def initialAssignment3(assignment: MHashMap[Term, Option[String]]) : MHashMap[Term, Option[String]] = {
      def getInitialAssignment3(term: Term) : Option[String] = {
        if (term.isConstant) {return strDatabase.term2Str(term)}
        if (assignment.contains(term)) {return assignment(term)}
        val vectors = concatPerRes.getOrElse(term, List())
        val assign = vectors.flatMap { vector =>
          vector.filter(_ != term).collect {
            case t if concatPerRes.contains(t) => getInitialAssignment3(t) match {
              case Some(s) => s
              case None => ""
            }
            case t if t.isConstant => strDatabase.term2Str(t) match {
              case Some(s) => s
              case None => ""
            }
            case _ => ""
          }
        }.mkString
        assignment(term) = Some(assign)
        return Some(assign)
      }
      concatPerRes.keys.foreach(getInitialAssignment3)

      for (concat <- concatPerRes) {
        for (element <- concat._2) {
          if (!assignment.contains(element.tail.tail.head)) {assignment.update(element.tail.tail.head, Some(strDatabase.term2Str(element.tail.tail.head).getOrElse("")))}
          if (!assignment.contains(element.tail.head)) {assignment.update(element.tail.head, Some(strDatabase.term2Str(element.tail.head).getOrElse("")))}
          if (!assignment.contains(element.head)) {assignment.update(element.head, Some(strDatabase.term2Str(element.head).getOrElse("")))}
        }
      }

      for (regex <- posRegularExpressions) {
        assignment.update(regex.head, Some(strDatabase.term2Str(regex.head).getOrElse("")))
      }
      for (regex <- negRegularExpressions) {
        assignment.update(regex.head, Some(strDatabase.term2Str(regex.head).getOrElse("")))
      }
      for (replace <- replacesLits) {
        assignment.update(replace.tail.tail.tail.head, Some(strDatabase.term2Str(replace.tail.tail.head).getOrElse("")))
        assignment.update(replace.tail.tail.head, Some(strDatabase.term2Str(replace.tail.tail.head).getOrElse("")))
        assignment.update(replace.tail.head, Some(strDatabase.term2Str(replace.tail.head).getOrElse("")))
        assignment.update(replace.head, Some(strDatabase.term2Str(replace.head).getOrElse("")))
      }

      return assignment
    }


    // transforms wordequations into regular expressions based on current assignment
    def wordEquationIntoRegex(assignment : MHashMap[Term, Option[String]]) : Unit = {
      constructedRegexesWordequations.clear()
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
          constructedRegexesWordequations += ((we3, aut, Some(wordequation)))
        }
      }
    }

    def solveReplace(assignment: MHashMap[Term, Option[String]]) : MHashMap[Term, Option[String]] = {
      for (replace <- replacesLits) {
        val left = replace.tail.tail.tail.head
        val right1 = assignment.get(replace.head).flatten
        val right2 = assignment.get(replace.tail.head).flatten
        val right3 = assignment.get(replace.tail.tail.head).flatten

        (right1, right2, right3) match {
          case (Some(x), Some(y), Some(z)) => {
            //val yy = if (y.isEmpty) "" else java.util.regex.Pattern.quote(y)
            //val zz = if (z.isEmpty) "" else java.util.regex.Pattern.quote(z)
            assignment.update(left, Some(x.replaceFirst(y,z)))
          }
        }
      }
      return assignment
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
      val acceptedWord = regex._2.getAcceptedWord
      val isAccepted = regex._2.apply(acceptedWord.get)
      val product = AutomataUtils.product(Seq(regex._2))
      val concat = AutomataUtils.concat(regex._2.asInstanceOf[BricsAutomaton], regex._2.asInstanceOf[BricsAutomaton])
      model.put(regex._1, Right(acceptedWord.get))
    }


    // scoring, solution if score == 0
    def score(assignment: MHashMap[Term, Option[String]]) : Int = {
      var score = 0
      for (concat <- concatPerRes) {
        for (element <- concat._2) {
           (assignment.get(element.tail.tail.head), assignment.get(element.head), assignment.get(element.tail.head)) match {
             case (Some(Some(x)),Some(Some(y)),Some(Some(z))) => if (x != y + z){score += 1
               }
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
          }
            if (!regex._2.apply(word)) {score += 1}
          case _ => {
            score += 1
          }
        }
      }
      for (replace <- replacesLits) {
        val left = assignment.get(replace.tail.tail.tail.head).flatten
        val right1 = assignment.get(replace.head).flatten
        val right2 = assignment.get(replace.tail.head).flatten
        val right3 = assignment.get(replace.tail.tail.head).flatten
        (left, right1, right2, right3) match {
          case (Some(a), Some(x), Some(y), Some(z)) => {
            //val yy = if (y.isEmpty) "" else java.util.regex.Pattern.quote(y)
            //val zz = if (z.isEmpty) "" else java.util.regex.Pattern.quote(z)
            if (a != x.replaceFirst(y, z)) {
              score += 1
            }
          }
          case _ => score += 1
        }
      }
      return score
    }

    def cH(term: Term) : Int = {
      if (term.isConstant) {return 0}
      else {return 1}
    }

    // scoring, solution if score == 0
    def complexityScore(assignment: MHashMap[Term, Option[String]]) : Int = {
      var score = 0
      for (concat <- concatPerRes) {
        for (element <- concat._2) {
          (assignment.get(element.tail.tail.head), assignment.get(element.head), assignment.get(element.tail.head)) match {
            case (Some(Some(x)),Some(Some(y)),Some(Some(z))) => if (x != y + z){
              score += (complexityMap.getOrElse(element.tail.head,cH(element.tail.head)) + complexityMap.getOrElse(element.head,cH(element.head)))
            }
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
          }
            if (!regex._2.apply(word)) {score += 1}
          case _ => {
            score += 1
          }
        }
      }
      for (replace <- replacesLits) {
        val left = assignment.get(replace.tail.tail.tail.head).flatten
        val right1 = assignment.get(replace.head).flatten
        val right2 = assignment.get(replace.tail.head).flatten
        val right3 = assignment.get(replace.tail.tail.head).flatten
        (left, right1, right2, right3) match {
          case (Some(a), Some(x), Some(y), Some(z)) => {
            //val yy = if (y.isEmpty) "" else java.util.regex.Pattern.quote(y)
            //val zz = if (z.isEmpty) "" else java.util.regex.Pattern.quote(z)
            if (a != x.replaceFirst(y, z)) {
              score += 1
            }
          }
          case _ => score += 1
        }
      }
      return score
    }


    def stringToSeqInt(str: String) : Seq[Int] = {
      var seqint : Seq[Int] = Seq()
      str match {
        case "" => Vector()
        case x => for ( c <- x.toCharArray) {
          seqint = seqint :+ c.toInt
        }
      }
      return seqint
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
        Seq()
      }
      val keyArray = assignment.keysIterator.toArray
      val keyIndex : Int = ThreadLocalRandom.current().nextInt(assignment.keySet.size)
      if ((!keyArray(keyIndex).isConstant) & assignment.get(keyArray(keyIndex)).flatten.isDefined){
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
      if (candidates.isEmpty) {/*println("UNASSIGN FAILED")*/}
      else {
        val keyIndex: Int = ThreadLocalRandom.current().nextInt(candidates.size)
        assignment.update(candidates(keyIndex), None)
      }
    }

    def constantStrVarResolveConflict (strVar :Term, usedRegexes : ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])], assignment : MHashMap[Term, Option[String]]) : MHashMap[Term, Option[String]] = {
      for (regex <- usedRegexes) {
        if (regex._1 == strVar && regex._2.isEmpty) {
          val unassignableTerms = new ArrayBuffer[(Term, Term, Term)]
          unassignableTerms += regex._3.getOrElse((strVar, strVar, strVar)) // Problem with None ?? NO I guess
          unassignRandomRelevant(assignment, unassignableTerms)
          wordEquationIntoRegex(assignment)
          val usedRegexes2 = regexes ++ constructedRegexesWordequations
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
            case None => //println("NONE ", regex._3)
          }
        }
      }
      return (aut, wordequation)
    }

    def regexAssignmentIntoWordequationAssignment(acceptedWord : Option[Seq[Int]], wordequations : ArrayBuffer[(Term, Term, Term)], assignment : MHashMap[Term, Option[String]], strVar : Term) : MHashMap[Term, Option[String]] = {
      var reorder = false
      val acceptedWordString = acceptedWord.map(_.map(_.toChar).mkString).getOrElse("") //should never be None
      val len = acceptedWordString.length
      val workingAssignment = assignment

      if (wordequations.isEmpty && !strVar.isConstant){
        workingAssignment.update(strVar, Some(acceptedWordString))
      }

      breakable { for (we <- wordequations) {
        if (workingAssignment.get(we._3) == Some(None)){
          workingAssignment.update(we._3, Some(acceptedWordString))
        }
        (workingAssignment.get(we._1), workingAssignment.get(we._2)) match {
          case (Some(Some(x)),Some(Some(y))) => if (acceptedWordString != x+y) {
             }
          case (Some(Some(x)), Some(None)) =>
            if (x.length > len) {
            }
            else if (x == acceptedWordString.substring(0,x.length)) {
              workingAssignment.update(we._2, Some(acceptedWordString.substring(x.length)))
              reorder = true
              break
            }
            else {
            }
          case (Some(None), Some(Some(x))) =>
            if (x.length > len) {
            }
            else if (x == acceptedWordString.substring(len-x.length)) {
              workingAssignment.update(we._1, Some(acceptedWordString.substring(0,len-x.length)))
              reorder = true
              break
            }
            else {
            }
          case (Some(None), Some(None)) =>

            val constructedRegexesTemp = constructedRegexesWordequations
            wordEquationIntoRegex(workingAssignment)
            val tempRegexes = constructedRegexesWordequations
            constructedRegexesWordequations = constructedRegexesTemp
            val we1Intersection = makeStrVarIntersection(we._1, tempRegexes)
            val we1AcceptedWord = we1Intersection._1.getAcceptedWord
            val we1AcceptedWordString = we1AcceptedWord.map(_.map(_.toChar).mkString).getOrElse("")

            val we2Intersection = makeStrVarIntersection(we._2, tempRegexes)
            val we2AcceptedWord = we2Intersection._1.getAcceptedWord
            val we2AcceptedWordString = we2AcceptedWord.map(_.map(_.toChar).mkString).getOrElse("")

            if (acceptedWordString.startsWith(we1AcceptedWordString)) {
              workingAssignment.update(we._1, Some(we1AcceptedWordString))
              workingAssignment.update(we._2, Some(acceptedWordString.substring(we1AcceptedWordString.length)))
            } else if (acceptedWordString.endsWith(we2AcceptedWordString)) {
              workingAssignment.update(we._2, Some(we2AcceptedWordString))
              workingAssignment.update(we._1, Some(acceptedWordString.substring(0,len-we2AcceptedWordString.length)))
            } else {
              val randomSplitIndex = ThreadLocalRandom.current().nextInt(len)
              workingAssignment.update(we._1, Some(acceptedWordString.substring(0, randomSplitIndex)))
              workingAssignment.update(we._2, Some(acceptedWordString.substring(randomSplitIndex)))
            }
            reorder = true
            break
        }
      } }
      if (reorder) {
        val newWordequations = orderWordequations(workingAssignment, wordequations)
        return regexAssignmentIntoWordequationAssignment(acceptedWord, newWordequations, workingAssignment, strVar)
      }
      return workingAssignment
    }




    // main loop starts here

    //assignment = initialAssignmentAllEmpty(assignment)
    //assignment = initialAssignment2(assignment)
    assignment = initialAssignment3(assignment)

    if (complexityScore(assignment) == 0) {
      assignmentToModel(assignment, model)
      return equalityPropagator.handleSolution(goal, model.toMap)
    }

    val recentScores = new FixedSizeQueue[Int](maxQueueSize)
    val previousAssignments = new FixedSizeQueue[MHashMap[Term, Option[String]]](tabooSize)

    var preImproveAssign = new MHashMap[Term, Option[String]]
    var postImproveAssign = new MHashMap[Term, Option[String]]
    val prohibitedAssignments = new ArrayBuffer[MHashMap[Term, Option[String]]]


    while (i < maxIterations) {
      previousAssignments.enqueue(assignment)
      wordEquationIntoRegex(assignment)
      var usedRegexes = regexes ++ constructedRegexesWordequations
      var choice = new MHashMap[MHashMap[Term, Option[String]], Int]
      for (strVar <- assignment.keys) {
        if (!strVar.isConstant) {
          var existsEmpty = false
          breakable {
            for (regex <- constructedRegexesWordequations) {
              if (regex._1 == strVar && regex._2.isEmpty) {
                existsEmpty = true
                break
              }
            }
            for (regex <- regexes) {
              val strVarString = assignment(strVar)
              strVarString match {
                case Some(x) => val strVarSeqInt = stringToSeqInt(x)
                  if (regex._1 == strVar && !regex._2.apply(strVarSeqInt)) {
                    existsEmpty = true
                    break
                  }
                case None => //if regex empty UNSAT
              }
            }
          }
          if (existsEmpty) {
            var newAssignment = assignment
            newAssignment.update(strVar, None)
            wordEquationIntoRegex(newAssignment)
            usedRegexes = regexes ++ constructedRegexesWordequations

            var strVarIntersection = makeStrVarIntersection(strVar, usedRegexes)
            var print = false //debug
            while (strVarIntersection._1.isEmpty) {
              print = true //debug
              unassignRandomRelevant(newAssignment, strVarIntersection._2)
              wordEquationIntoRegex(newAssignment)
              usedRegexes = regexes ++ constructedRegexesWordequations
              strVarIntersection = makeStrVarIntersection(strVar, usedRegexes)
            }
            var strVarRegexAssignment = strVarIntersection._1.getAcceptedWord
            val orderedWordequations = orderWordequations(newAssignment, strVarIntersection._2)
            val strVarAssignment = regexAssignmentIntoWordequationAssignment(strVarRegexAssignment, orderedWordequations, newAssignment, strVar) //could probably just be newAssignment
            newAssignment = newAssignment ++ strVarAssignment
            newAssignment = solveReplace(newAssignment)
            val currentScore: Int = complexityScore(newAssignment)
            if (currentScore == 0) {
              assignmentToModel(newAssignment, model)
              return equalityPropagator.handleSolution(goal, model.toMap)
            }
            choice.update(newAssignment, currentScore)
          }
        }
        else { //strVar is constant
          var newAssignment = assignment
          newAssignment = constantStrVarResolveConflict(strVar, usedRegexes, newAssignment)

          var strVarIntersection = makeStrVarIntersection(strVar, usedRegexes)
          var print = false //debug
          while (strVarIntersection._1.isEmpty) {
            print = true //debug
            unassignRandomRelevant(newAssignment, strVarIntersection._2)
            wordEquationIntoRegex(newAssignment)
            usedRegexes = regexes ++ constructedRegexesWordequations
            strVarIntersection = makeStrVarIntersection(strVar, usedRegexes)
          }
          var strVarRegexAssignment = strVarIntersection._1.getAcceptedWord
          val orderedWordequations = orderWordequations(newAssignment, strVarIntersection._2)
          val strVarAssignment = regexAssignmentIntoWordequationAssignment(strVarRegexAssignment, orderedWordequations, newAssignment, strVar) //could probably just be newAssignment
          newAssignment = newAssignment ++ strVarAssignment
          newAssignment = solveReplace(newAssignment)
          val currentScore: Int = complexityScore(newAssignment)
          if (currentScore == 0) {
            assignmentToModel(newAssignment, model)
            return equalityPropagator.handleSolution(goal, model.toMap)
          }
          choice.update(newAssignment, currentScore)
        }
      }

      if (choice.nonEmpty) {
        if (recentScores.size != maxQueueSize || !recentScores.allSame) {
          if (choice.values.min < complexityScore(assignment)) {
            preImproveAssign = assignment
            val minValue = choice.values.min
            val minElements = choice.filter { case (_, value) => value == minValue }.toSeq
            val randomElement = minElements(ThreadLocalRandom.current().nextInt(minElements.length))
            postImproveAssign = randomElement._1
            assignment = randomElement._1
            recentScores.enqueue(randomElement._2)
          }
          else {
            val minValue = choice.values.min
            val minElements = choice.filter { case (_, value) => value == minValue }.toSeq
            val randomElement = minElements(ThreadLocalRandom.current().nextInt(minElements.length))
            assignment = randomElement._1
            recentScores.enqueue(randomElement._2)
          }
        }
        else {
          assignment = preImproveAssign
          prohibitedAssignments += postImproveAssign
          recentScores.enqueue(complexityScore(assignment))
        }
      }
      i += 1
    }

    return List(Plugin.AddFormula(Conjunction.TRUE))
  }

}