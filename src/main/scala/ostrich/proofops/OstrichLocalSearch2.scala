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
import ostrich.automata.BricsAutomaton.{fromString, makeAnyString}
import ostrich.automata.{AutomataUtils, Automaton, BricsAutomaton}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.{HashMap => MHashMap}
import scala.concurrent.forkjoin.ThreadLocalRandom

class OstrichLocalSearch2(goal : Goal,
                         theory : OstrichStringTheory,
                         flags : OFlags)  {
  import TerForConvenience._
  import theory.{FunPred, StringSort, _str_++, str_in_re, str_in_re_id, autDatabase, _str_len, int_to_str, strDatabase, str_prefixof, str_replace, str_suffixof, str_to_int}

  implicit val order = goal.order

  val facts        = goal.facts
  val predConj     = facts.predConj
  val concatLits   = predConj.positiveLitsWithPred(_str_++)
  val posRegularExpressions = predConj.positiveLitsWithPred(str_in_re_id)
  //println("posRegEx", posRegularExpressions)
  val negRegularExpressions = predConj.negativeLitsWithPred(str_in_re_id)
  val concatPerRes = concatLits groupBy (_(2))
  val replacesLits = predConj.positiveLitsWithPred(FunPred(str_replace))
  val lengthLits   = predConj.positiveLitsWithPred(_str_len)
  val lengthMap    = (for (a <- lengthLits.iterator) yield (a(0), a(1))).toMap
  private val equalityPropagator = new OstrichEqualityPropagator(theory)

  def resolveConcat(t : LinearCombination)
  : Option[(LinearCombination, LinearCombination)] =
    for (lits <- concatPerRes get t) yield (lits.head(0), lits.head(1))

  def explore : Seq[Plugin.Action] = {
    val model = new MHashMap[Term, Either[IdealInt, Seq[Int]]]

    val regexes    = new ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]
    var constructedRegexesWordequations = new ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]

    var assignment = new MHashMap[Term, Option[String]]

    // only assign constant else None
    def initialAssignment2(assignment: MHashMap[Term, Option[String]]) : MHashMap[Term, Option[String]] = {
      for (concat <- concatPerRes) {
        for (element <- concat._2) {
          assignment.update(element.tail.tail.head, Some(strDatabase.term2Str(element.tail.tail.head)).flatten)
          assignment.update(element.tail.head, Some(strDatabase.term2Str(element.tail.head)).flatten)
          assignment.update(element.head, Some(strDatabase.term2Str(element.head)).flatten)
        }
      }
      for (regex <- posRegularExpressions) {
        assignment.update(regex.head, Some(strDatabase.term2Str(regex.head)).flatten)
      }
      for (regex <- negRegularExpressions) {
        assignment.update(regex.head, Some(strDatabase.term2Str(regex.head)).flatten)
      }
      for (replace <- replacesLits) {
        assignment.update(replace.tail.tail.tail.head, Some(strDatabase.term2Str(replace.tail.tail.head)).flatten)
        assignment.update(replace.tail.tail.head, Some(strDatabase.term2Str(replace.tail.tail.head)).flatten)
        assignment.update(replace.tail.head, Some(strDatabase.term2Str(replace.tail.head)).flatten)
        assignment.update(replace.head, Some(strDatabase.term2Str(replace.head)).flatten)
      }
      return assignment
    }

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

    def decodeRegexId(a : Atom, complemented : Boolean) : Unit = a(1) match {
      case LinearCombination.Constant(id) => {
        val autOption =
          if (complemented)
            autDatabase.id2ComplementedAutomaton(id.intValueSafe)
          else {
            autDatabase.id2Automaton(id.intValueSafe)
          }

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
        //println("REGEX", regex)
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
    for (concat <- concatPerRes){
      //println(concat)
    }

    def score(assignment: MHashMap[Term, Option[String]]) : Int = {
      var score = 0
      for (concat <- concatPerRes) {
        for (element <- concat._2) {
          (assignment.get(element.tail.tail.head), assignment.get(element.head), assignment.get(element.tail.head)) match {
            case (Some(Some(x)),Some(Some(y)),Some(Some(z))) => if (x != y + z){score += 1
              //println(element)
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
        //println(left, right1, right2, right3)
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

    def solveWeWith2AssignedParts(assignment: MHashMap[Term, Option[String]]) : MHashMap[Term, Option[String]] = {
      val oldAssignment = assignment
      for (concat <- concatPerRes) {
        for (element <- concat._2) {
          (assignment.get(element.tail.tail.head).flatten, assignment.get(element.tail.head).flatten, assignment.get(element.head).flatten) match {
            case (Some(x),Some(y),Some(z)) => if (x != y + z) {println("ERROR")}
            case (Some(x),Some(y),None) => assignment.update(element.head,Some(x.substring(y.length)))
            case (Some(x),None,Some(z)) => assignment.update(element.tail.head,Some(x.substring(0,x.length-z.length)))
            case (None,Some(y),Some(z)) => assignment.update(element.tail.tail.head, Some(y+z))
            case _ => //nothing
          }
        }
      }
      if (oldAssignment != assignment){solveWeWith2AssignedParts(assignment)}
      else {return assignment}
    }

    def intersectWeRegexesWithFixedRegexes(fixedRegexes : ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])], weRegexes : ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]) : ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])] = {
      val intersectedRegexes = new ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]
      for (regex <- weRegexes) {
        var aut = regex._2
        for (fixedRegex <- fixedRegexes) {
          aut = aut.&(fixedRegex._2)
        }
        intersectedRegexes += ((regex._1, aut, regex._3))
      }
      return intersectedRegexes
    }

    def seqIntToString(word: Seq[Int]) : String = {
      val seqString = for (c <- word.toIndexedSeq) yield c.toChar.toString
      val string = seqString.mkString("")
      return string
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

    def getAcceptedWords(regexes : ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]) : ArrayBuffer[(Term, String)] = {
      val acceptedWords = new ArrayBuffer[(Term, String)]
      for (regex <- regexes) {
        val aw = regex._2.getAcceptedWord.getOrElse(Seq())
        val awString = seqIntToString(aw)
        acceptedWords += ((regex._1, awString))
      }
      return acceptedWords
    }

    //checks if there is already a conflict in assigned variables, ignores unassigned stuff
    def checkAssignmentViable(assignment : MHashMap[Term, Option[String]]) : Boolean = {
      for (concat <- concatPerRes) {
        for (element <- concat._2) {
          (assignment.get(element.tail.tail.head).flatten, assignment.get(element.tail.head).flatten, assignment.get(element.head).flatten) match {
            case (Some(x), Some(y), Some(z)) => if (x != y + z) {
              return false
            }
            case (Some(x), Some(y), None) => if (x.substring(0, y.length) != y) {
              return false
            }
            case (Some(x), None, Some(z)) => if (x.substring(x.length - z.length) != z) {
              return false
            }
          }
        }
      }
      for (regex <- regexes) {
        if (assignment.get(regex._1) != None) {
          // should never get to getOrElse part
          val assignmentString : String = (assignment.get(regex._1).flatten).getOrElse("")
          val assignmentSeqInt = stringToSeqInt(assignmentString)
          if (!regex._2.apply(assignmentSeqInt)) {return false}
        }
      }
      return true
    }

    def tryAssignments(assignment: MHashMap[Term, Option[String]], acceptedWords : ArrayBuffer[(Term, String)]) : MHashMap[Term, Option[String]] = {
      var newAssignment = assignment
      val assignments = new ArrayBuffer[(MHashMap[Term, Option[String]],Int)]
      for (element <- acceptedWords) {
        newAssignment.update(element._1, Some(element._2))
        if (checkAssignmentViable(newAssignment)) {
          assignments += ((newAssignment, score(newAssignment)))
        }
        newAssignment = assignment
      }
      if (assignments.isEmpty) {
        return assignment
        // return new MHashMap[Term, Option[String]]()
      }
      else {
        val minValue = assignments.map(_._2).min
        val minElements = assignments.filter(_._2 == minValue)
        val randomElement = minElements(ThreadLocalRandom.current().nextInt(minElements.length))
        return randomElement._1
      }
    }

    def solveWithCurrentFixedRegexes(maxTries : Int, fixedRegexes : ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]) : Option[MHashMap[Term, Option[String]]] = {
      var tries : Int = 0
      while (tries <= maxTries) {

        wordEquationIntoRegex(assignment)
        val weRegexes = constructedRegexesWordequations
        val intersectedRegexes = intersectWeRegexesWithFixedRegexes(fixedRegexes, weRegexes)
        var acceptedWords = getAcceptedWords(intersectedRegexes)
        // if no accepting words in intersection with fixed found
        // then get accepted words for regexes alone
        if (acceptedWords.isEmpty){
          acceptedWords = getAcceptedWords(weRegexes)
        }
        val newAssignment = tryAssignments(assignment, acceptedWords)
        if (score(newAssignment) == 0) {
         return Some(newAssignment)
        }
        assignment = newAssignment
        tries += 1
      }
      return None
    }

    //get all the chars that may be used
    def getUsedChars() : Set[Char] = {
      val charSet : Set[Char] = Set()
      for (regex <-regexes){
        val aut = regex._2
        //println(aut.)
      }



      return charSet
    }

    // gives None as splitting, is fine as long as we only call this with nonsplitt Wes
    // might need changing later
    def getWeWithDifferentConstParts(weRegexes : ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])], currAssignment : MHashMap[Term, Option[String]]): (ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)]) = {
      val weConstx = new ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)]
      val weConsty = new ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)]
      val weConstz = new ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)]
      val weNoConst = new ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)]
      for (we <- weRegexes) {
        we._3 match {
          case Some((x, y, z)) if currAssignment.get(x).flatten.isDefined && currAssignment.get(y).flatten.isEmpty && currAssignment.get(z).flatten.isEmpty =>
            weConstx += ((we._1, we._2, (x,y,z), None, 1))
          case Some((x, y, z)) if currAssignment.get(y).flatten.isDefined && currAssignment.get(x).flatten.isEmpty && currAssignment.get(z).flatten.isEmpty =>
            weConsty += ((we._1, we._2, (x,y,z), None, 2))
          case Some((x, y, z)) if currAssignment.get(z).flatten.isDefined && currAssignment.get(x).flatten.isEmpty && currAssignment.get(y).flatten.isEmpty =>
            weConstz += ((we._1, we._2, (x,y,z), None, 3))
          case Some((x, y, z)) if currAssignment.get(x).flatten.isEmpty && currAssignment.get(y).flatten.isEmpty && currAssignment.get(z).flatten.isEmpty =>
            weNoConst += ((we._1, we._2, (x,y,z), None, 4))
          case _ => // If none of the conditions match, do nothing
        }
      }
      return (weConstx, weConsty, weConstz, weNoConst)
    }

    def splitting(currSplitWes : ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], assignment: MHashMap[Term, Option[String]]) : (ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], MHashMap[Term, Option[String]]) = {
      def splittingConstx(currSplitWes : ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], assignment: MHashMap[Term, Option[String]], currWe : (Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)) : (ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], MHashMap[Term, Option[String]]) = {
        //getOrElse never actually used
        val const = assignment(currWe._3._1).getOrElse("")
        if (currWe._4.isDefined) {
          val currSplit = currWe._4.getOrElse(("","",""))
          // we: x = y z, first: x = x eps, last: x = eps x
          if (currSplit == (const, "", const)){
            // all splits for this we tried
            // next split for previous we
            assignment.update(currWe._3._2, None)
            assignment.update(currWe._3._3, None)
            currSplitWes.trimEnd(1)
            splitting(currSplitWes,assignment)
          }
          else {
            val lastChary = currSplit._2.last
            val newy = currSplit._2.dropRight(1)
            val newz = lastChary + currSplit._3
            val newSplit = (const, newy, newz)
            assignment.update(currWe._3._2, Some(newy))
            assignment.update(currWe._3._3, Some(newz))
            currSplitWes.trimEnd(1)
            currSplitWes += ((currWe._1, currWe._2, currWe._3, Some(newSplit), 1))
            return (currSplitWes, assignment)
          }
        }
        else {
          //first split
          val newSplit = (const, const, "")
          assignment.update(currWe._3._2, Some(const))
          assignment.update(currWe._3._3, Some(""))
          currSplitWes.trimEnd(1)
          currSplitWes += ((currWe._1, currWe._2, currWe._3, Some(newSplit), 1))
          return (currSplitWes, assignment)
        }
      }
      def splittingConsty(currSplitWes : ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], assignment: MHashMap[Term, Option[String]], currWe : (Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)) : (ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], MHashMap[Term, Option[String]]) = {
        //start with commonprefix ?
        //val commonPrefix = dk.brics.automaton.SpecialOperations.getCommonPrefix(currWe._2)
        return (currSplitWes, assignment)
      }
      def splittingConstz(currSplitWes : ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], assignment: MHashMap[Term, Option[String]], currWe : (Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)) : (ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], MHashMap[Term, Option[String]]) = {
        return (currSplitWes, assignment)
      }
      def splittingNoConst(currSplitWes : ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], assignment: MHashMap[Term, Option[String]], currWe : (Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)) : (ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)], MHashMap[Term, Option[String]]) = {
        return (currSplitWes, assignment)
      }

      var chosenWe : (Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int) = null
      //select a WE to perform Automata splitting on
      //prefer const left side that have not been split yet

      //get  not split wes
      wordEquationIntoRegex(assignment)
      val weRegexes = constructedRegexesWordequations
      val notSplitWes = new ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]
      for (we <- weRegexes) {
        val exists = currSplitWes.exists {
          case (term, aut, weTerms, _, _) => term == we._1 && aut == we._2 && we._3.contains(weTerms)
          case _ => false
        }
        if (!exists) {
          notSplitWes += we
        }
      }

      //get different const parts
      val (weNotSplitConstLeftSide, weNotSplitConstRightSidey, weNotSplitConstRightSidez, weNotSplitNoConst) = getWeWithDifferentConstParts(notSplitWes, assignment)

      //choose we to perform splitting on
      if (weNotSplitConstLeftSide.nonEmpty) {
        chosenWe = weNotSplitConstLeftSide(ThreadLocalRandom.current().nextInt(weNotSplitConstLeftSide.length))
        currSplitWes.append(chosenWe)
      }
      else if (weNotSplitConstRightSidey.nonEmpty) {
        chosenWe = weNotSplitConstRightSidey(ThreadLocalRandom.current().nextInt(weNotSplitConstRightSidey.length))
        currSplitWes.append(chosenWe)
      }
      else if (weNotSplitConstRightSidez.nonEmpty) {
        chosenWe = weNotSplitConstRightSidez(ThreadLocalRandom.current().nextInt(weNotSplitConstRightSidez.length))
        currSplitWes.append(chosenWe)
      }
      else if (weNotSplitNoConst.nonEmpty) {
        chosenWe = weNotSplitNoConst(ThreadLocalRandom.current().nextInt(weNotSplitNoConst.length))
        currSplitWes.append(chosenWe)
      }
      else {
        chosenWe = currSplitWes.last
      }

      chosenWe._5 match {
        case 1 => return splittingConstx(currSplitWes, assignment, chosenWe)
        case 2 => return splittingConsty(currSplitWes, assignment, chosenWe)
        case 3 => return splittingConstz(currSplitWes, assignment, chosenWe)
        case 4 => return splittingNoConst(currSplitWes, assignment, chosenWe)
        case _ => return (currSplitWes, assignment) //ERROR

      }



    }
/*
    def getunfulfilledWEs(assignment : MHashMap[Term, Option[String]]) : ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])] = {
      val unfulfilledWEs = new ArrayBuffer[(Term, Automaton, Option[(Term, Term, Term)])]
      for (concat <- concatPerRes) {
        for (element <- concat._2) {
          (assignment.get(element.tail.tail.head).flatten, assignment.get(element.tail.head).flatten, assignment.get(element.head).flatten) match {
            case (Some(x),Some(y),Some(z)) => //nothing
            case _ => unfulfilledWEs += ((element.tail.tail.head,)
          }
        }
      }
    }
 */
    def mainloop(maxTries : Int = 100) : Option[Seq[Plugin.Action]] = {
      var tries : Int = 0
      assignment = initialAssignment2(new MHashMap[Term, Option[String]])
      assignment = solveWeWith2AssignedParts(assignment)

      if (score(assignment) == 0) {
        //TODO: handle solution
      }

      // Regexes of the initial formula
      val fixedRegexesSafe = regexes

      // Computes Regexes of WE based on the assignment (currently all assignments have to be right)
      wordEquationIntoRegex(assignment)
      val weRegexesSafe = constructedRegexesWordequations

      // now try to solve WEs by intersecting WE-Regexes with all fixed Regexes
      val intersectedRegexesSafe = intersectWeRegexesWithFixedRegexes(fixedRegexesSafe, weRegexesSafe)

      // get accepted word for each WE-Regex intersected with fixed Regexes
      val acceptedWords = getAcceptedWords(intersectedRegexesSafe)

      // there can't be any mistakes in the assignment yet
      val assignmentSafe = assignment

      // try to solve with current fixed Regexes
      val solution = solveWithCurrentFixedRegexes(maxTries, fixedRegexesSafe)

      //solution found
      if (solution.isDefined) {
        //Todo: handle Solution
      }

      // could not solve with current fixed Regexes
      // Automata Splitting

      //[Term, Aut, We, currSplit, Type]
      // Type: 1=constx, 2=consty, 3=constz, 4=noconst
      var currSplitWes = new ArrayBuffer[(Term, Automaton, (Term, Term, Term), Option[(String, String, String)], Int)]

      //revert assignment to a safe assignment
      assignment = assignmentSafe

      val (newSplitWes, newAssignment) = splitting(currSplitWes, assignment)



      //Todo: Splitting on selected WE
      // Adding disjunct to fixedRegexes
      // Try to solve
      // Loop this process



      //pick a not fulfilled WE
      //val unfulfilledWEs =




      //Todo: handle solution
      return Some(equalityPropagator.handleSolution(goal, model.toMap))

      }




    // TESTING AREA
    tryAssignments(new MHashMap[Term, Option[String]], new ArrayBuffer[(Term, String)])
    val test = getUsedChars()
















    val foundSolution = false
    if (foundSolution){
      equalityPropagator.handleSolution(goal, model.toMap)
    }
    else{
      Seq()
    }
  }

}
