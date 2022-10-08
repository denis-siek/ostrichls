package ostrich.automata.afa2.concrete

import ostrich.automata.afa2.{Left, Right, StepTransition, Transition}

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet}

//object AFA2 {

  /*
  //TODO: Is this used?
  object Position extends Enumeration {
    val LeftMost, Any, RightMost = Value
  }
  */


/*
Existential nondeterminism is implemented by having multiple transitions in the sequence.
Universal   nondeterminism is implemented by having multiple target states in Transition.
 */
case class AFA2(initialStates : Seq[Int],
                finalStates   : Seq[Int],
                transitions   : Map[Int, Seq[StepTransition]]) {

  override def toString: String = {
    val res = new mutable.StringBuilder()
    res.append("Initial states: " + initialStates + "\n")
    res.append("Final states: " + finalStates + "\n")
    for (tr <- transitions) {
      res.append(tr._1 + "goes to \n")
      for (t <- tr._2) res.append(t)
    }
    res.toString()
  }

  assert(!initialStates.isEmpty)

  val states = {
    val states = new MHashSet[Int]

    states ++= initialStates
    states ++= finalStates

    for ((source, ts)                  <- transitions.iterator;
         StepTransition(_, _, targets) <- ts.iterator;
         target                        <- targets.iterator) {
      states += source
      states += target
    }

    states.toIndexedSeq.sorted
  }

  lazy val fwdReachable = {
    val reachable = new MHashSet[Int]
    reachable ++= initialStates

    var oldSize = 0
    while (oldSize < reachable.size) {
      oldSize = reachable.size

      for (s                             <- reachable.toList;
           StepTransition(_, _, targets) <- transitions.getOrElse(s, List())) {
        reachable ++= targets
      }
    }

    reachable.toSet
  }

  lazy val bwdReachable = {
    val reachable = new MHashSet[Int]
    reachable ++= finalStates

    var oldSize = 0
    while (oldSize < reachable.size) {
      oldSize = reachable.size

      for ((source, ts)                  <- transitions.iterator;
           if !(reachable contains source);
           StepTransition(_, _, targets) <- ts.iterator)
        if (targets forall reachable)
          reachable += source
    }

    reachable.toSet
  }

  lazy val reachableStates =
    fwdReachable & bwdReachable


  def minimizeStates() : AFA2 = {

    def minimizeStatesStep(aut: AFA2): AFA2 = {

      val flatTrans = for ((st, ts) <- aut.transitions.toSeq) yield (ts.toSet, st)

      // Map keeping track of eliminatedState => stateKept
      val stateMap = mutable.HashMap[Int, Int]()

      val transStateMap = flatTrans.groupBy(_._1).mapValues(l => l map (_._2))
      println("transStateMap:\n" + transStateMap)
      /*
    The above map is still rough, as in the values can contain states that are final, nonfinal, noninitial, initial
    We have to split them in group of states:
    - plain : neither final nor initial
    - fi : final and initial
    - f : final
    - i : initial
     */
      var plainTSM = transStateMap.mapValues(_.filter(x => !aut.initialStates.contains(x) && !aut.finalStates.contains(x)))
      var fiTSM = transStateMap.mapValues(_.filter(x => aut.initialStates.contains(x) && aut.finalStates.contains(x)))
      var fTSM = transStateMap.mapValues(_.filter(x => !aut.initialStates.contains(x) && aut.finalStates.contains(x)))
      var iTSM = transStateMap.mapValues(_.filter(x => aut.initialStates.contains(x) && !aut.finalStates.contains(x)))

      plainTSM = plainTSM.filter(_._2.nonEmpty)
      fiTSM = fiTSM.filter(_._2.nonEmpty)
      fTSM = fTSM.filter(_._2.nonEmpty)
      iTSM = iTSM.filter(_._2.nonEmpty)

      println("plainTSM:\n" + plainTSM)
      println("fiTSM:\n" + fiTSM)
      println("fTSM:\n" + fTSM)
      println("iTSM:\n" + iTSM)


      for ((_, sts) <- plainTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- fiTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- fTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- iTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      /* Now in the keyset of StateMap contains all and only states that has to be removed.
    The removal strategy is the following:
    (1) filter the transitions map with states to be removed;
    (2) scan such reduced transitions and map the arrival states with stateMap
     */
      val toBeRemoved = stateMap.keySet.toSet
      println("Removed map:\n" + stateMap)
      println("To be removed:\n" + toBeRemoved)
      // All other states have to be mapped to themsleves!
      for (s <- aut.states.toSet -- toBeRemoved) stateMap += ((s, s))
      val reducedTrans = aut.transitions.filterNot(x => toBeRemoved.contains(x._1))
      println("Reduced trans:\n" + reducedTrans)
      val newTrans = reducedTrans.mapValues(_.map(x => StepTransition(x.label, x.step, x.targets.map(stateMap))))

      val newAut = AFA2(aut.initialStates, aut.finalStates, newTrans)

      newAut.restrictToReachableStates
    }

    def minimizeStatesStepOptimised(aut: AFA2) : AFA2 = {

      //val flatTrans = for ((st, ts) <- aut.transitions.toSeq) yield (ts.toSet, st)
      /*
      Problem: self-transitions do not allow to easily recognise states that have the same outgoing transitions.
      Therefore, is we have a self transition (7, StepTrans(->, [5], Seq(7))) we substitute it with
      (7, StepTrans(->, [5], Seq(SELF))) so they can be recognised.
       */
      val SELF = -5
      val aux = for ((st, ts) <- aut.transitions.toSeq) yield (ts.toSet, st)

      val flatTrans = aux.map{case (transSet, state) =>
        val selfMap: Map[Int, Int] = (for (s <- aut.states) yield (if (s==state) (s, SELF) else (s, s))).toMap
        val newTransSet = transSet.map(x => StepTransition(x.label, x.step, x.targets.map(selfMap)))
        (newTransSet, state)
      }

      // Map keeping track of eliminatedState => stateKept
      val stateMap = mutable.HashMap[Int, Int]()

      val transStateMap = flatTrans.groupBy(_._1).mapValues(l => l map (_._2))
      println("transStateMap:\n" + transStateMap)
      /*
    The above map is still rough, as in the values can contain states that are final, nonfinal, noninitial, initial
    We have to split them in group of states:
    - plain : neither final nor initial
    - fi : final and initial
    - f : final
    - i : initial
     */
      var plainTSM = transStateMap.mapValues(_.filter(x => !aut.initialStates.contains(x) && !aut.finalStates.contains(x)))
      var fiTSM = transStateMap.mapValues(_.filter(x => aut.initialStates.contains(x) && aut.finalStates.contains(x)))
      var fTSM = transStateMap.mapValues(_.filter(x => !aut.initialStates.contains(x) && aut.finalStates.contains(x)))
      var iTSM = transStateMap.mapValues(_.filter(x => aut.initialStates.contains(x) && !aut.finalStates.contains(x)))

      plainTSM = plainTSM.filter(_._2.nonEmpty)
      fiTSM = fiTSM.filter(_._2.nonEmpty)
      fTSM = fTSM.filter(_._2.nonEmpty)
      iTSM = iTSM.filter(_._2.nonEmpty)

      println("plainTSM:\n" + plainTSM)
      println("fiTSM:\n" + fiTSM)
      println("fTSM:\n" + fTSM)
      println("iTSM:\n" + iTSM)


      for ((_, sts) <- plainTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- fiTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- fTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- iTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      /* Now in the keyset of StateMap contains all and only states that has to be removed.
    The removal strategy is the following:
    (1) filter the transitions map with states to be removed;
    (2) scan such reduced transitions and map the arrival states with stateMap
     */
      val toBeRemoved = stateMap.keySet.toSet
      println("Removed map:\n" + stateMap)
      println("To be removed:\n" + toBeRemoved)
      // All other states have to be mapped to themsleves!
      for (s <- aut.states.toSet--toBeRemoved) stateMap += ((s, s))
      val reducedTrans = aut.transitions.filterNot(x => toBeRemoved.contains(x._1))
      println("Reduced trans:\n" + reducedTrans)
      val newTrans = reducedTrans.mapValues(_.map(x => StepTransition(x.label, x.step, x.targets.map(stateMap))))

      val newTransConverted = newTrans.map{ case (st, ts) =>
        val newTS = ts.map(x => StepTransition(x.label, x.step, x.targets.map(x => {if (x==SELF) st else x}) ))
        (st, newTS)
      }

      val newAut = AFA2(aut.initialStates, aut.finalStates, newTrans)

      newAut.restrictToReachableStates
    }


    var oldAut = this
    var newAut = minimizeStatesStep(oldAut)
    while (newAut.states.size != oldAut.states.size) {
      oldAut = newAut
      newAut = minimizeStatesStep(oldAut)
    }
    newAut

  }


  def restrictToReachableStates : AFA2 =
    if (reachableStates.size == states.size) {
      this
    } else {
      val newInitialPre =
        initialStates filter reachableStates
      val newInitial =
        if (newInitialPre.isEmpty)
          initialStates take 1
        else
          newInitialPre

      val newFinal =
        finalStates filter reachableStates
      val newTransitions =
        for ((source, ts) <- transitions;
             if (reachableStates contains source)) yield {
          val newTS =
            for (t@StepTransition(_, _, targets) <- ts;
                 if targets forall reachableStates)
            yield t
          source -> newTS
        }

      AFA2(newInitial, newFinal, newTransitions)
    }

  // Different categories of states:
  //
  // ir: initial,                       outgoing transitions go right
  // ll: incoming transitions go left,  outgoing transitions go left
  // lr: incoming transitions go left,  outgoing transitions go right
  // rl: incoming transitions go right, outgoing transitions go left
  // rr: incoming transitions go right, outgoing transitions go right
  // rf: incoming transitions go right, final

  lazy val (irStates, llStates, lrStates, rlStates, rrStates, rfStates) = {
    val leftIn, rightIn, leftOut, rightOut = new MHashSet[Int]

    for ((source, ts)                     <- transitions.iterator;
         StepTransition(_, step, targets) <- ts.iterator;
         target                           <- targets.iterator) {
      step match {
        case Left  => {
          leftOut  += source
          leftIn   += target
        }
        case Right => {
          rightOut += source
          rightIn  += target
        }
      }
    }

    val onlyLeftIn   = leftIn -- rightIn
    val onlyRightIn  = rightIn -- leftIn
    val onlyLeftOut  = leftOut -- rightOut
    val onlyRightOut = rightOut -- leftOut

    val anyIn        = leftIn ++ rightIn
    val anyOut       = leftOut ++ rightOut

    (initialStates.toSet & onlyRightOut.toSet -- anyIn -- finalStates,
      onlyLeftIn.toSet  & onlyLeftOut.toSet -- initialStates -- finalStates,
      onlyLeftIn.toSet  & onlyRightOut.toSet -- initialStates -- finalStates,
      onlyRightIn.toSet & onlyLeftOut.toSet -- initialStates -- finalStates,
      onlyRightIn.toSet & onlyRightOut.toSet -- initialStates -- finalStates,
      finalStates.toSet & onlyRightIn.toSet -- anyOut -- initialStates)
  }

  lazy val letters =
    (for ((source, ts)            <- transitions.iterator;
          StepTransition(l, _, _) <- ts.iterator)
    yield l).toSet.toIndexedSeq.sorted

}

case class ExtAFA2(initialStates    : Seq[Int],
                   finalLeftStates : Seq[Int],
                   finalRightStates   : Seq[Int],
                   transitions      : Map[Int, Seq[Transition]]) {

  assert(!initialStates.isEmpty)

  val states = {
    val states = new MHashSet[Int]

    states ++= initialStates
    states ++= finalLeftStates
    states ++= finalRightStates

    for ((source, ts) <- transitions.iterator;
         trans        <- ts.iterator;
         target       <- trans.targets.iterator) {
      states += source
      states += target
    }

    states.toIndexedSeq.sorted
  }

  lazy val letters =
    (for ((source, ts)            <- transitions.iterator;
          StepTransition(l, _, _) <- ts.iterator)
    yield l).toSet.toIndexedSeq.sorted

}

case class EpsAFA2(initialState: Int,
                   finalStates: Seq[Int],
                   transitions: Map[Int, Seq[Transition]]) {

  lazy val states = {
    val states = mutable.Set[Int](initialState)
    states ++= finalStates
    for ((s, ts) <- transitions;
         t <- ts) {
      states += s
      states ++= t.targets
    }
    states.toIndexedSeq.sorted
    states
  }
}