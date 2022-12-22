package ostrich.automata.afa2.symbolic

import ostrich.automata.BricsTLabelEnumerator
import ostrich.automata.afa2.concrete.AFA2
import ostrich.automata.afa2.symbolic.SymbToConcTranslator.toSymbDisjointAFA2
import ostrich.automata.afa2.{AFA2PrintingUtils, EpsTransition, Step, StepTransition, SymbTransition, Transition}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.util.Sorting


/*
Implements the symbolic to concrete translation by splitting all ranges so they do not
overlap and keeping a map from ranges to concrete symbols.
 */

object SymbToConcTranslator {

  def toSymbDisjointTrans(trans: Map[Int, Seq[SymbTransition]]): Map[Int, Seq[SymbTransition]] = {

    val flatTrans = for((st, ts) <- trans.toSeq;
                        t <- ts) yield (st, t)

    //println("Flat trans:\n" + flatTrans.map{t => t._2})

    val points = (for ((_, ts) <- trans.toSeq;
                      t <- ts) yield {
                        Seq(
                          (t.symbLabel.start, t.symbLabel.end, true), //open the interval
                          (t.symbLabel.end, t.symbLabel.start, false) //closes the interval
                        )
                      }).flatten.toSet.toArray

    Sorting.quickSort[(Int, Int, Boolean)](points)(Ordering[(Int, Boolean)].on(x => (x._1, x._3)))

    val it = points.iterator
    //println("Points:")
    //while(it.hasNext) println(it.next())

    val ranges = ArrayBuffer[Range]()
    var open = (-1, -1, false) // This is always (index_start, index_end). True means the interval is currently open, false it is closed.

    for ((index_1, index_2, b) <- points) {
      if (b==true) {
        val index_start=index_1
        val index_end=index_2
        if (open._1 != -1 && open._3==true && index_start>open._1) {
          assert(!(index_start > open._2), "Current open range: " + open + " I am seeing opening of: (" + index_1 +"," + index_2+")")
          ranges += Range(open._1, index_start)
        }
        if (index_end>open._2) open=(index_start, index_end, true)
        else open=(index_start, open._2, true)
      }
      else {
        if (open._3 == true) {
          val index_start = index_2
          val index_end = index_1
          ranges += (Range(open._1, index_end))
          assert(!(index_end > open._2), "Current open range: " + open + " I am seeing closure of: (" + index_2 + "," + index_1 + ")")
          if (index_end == open._2) open = (-1, -1, false)
          else open = (index_end, open._2, true)
        }
      }
    }

    val newTransFlat =
      for ((st, t) <- flatTrans;
         rg <- ranges;
         if (t.symbLabel.containsSlice(rg))) yield (st, SymbTransition(rg, t.step, t.targets))

    //println("New flat trans:\n"+ newTransFlat.map{t=>t._2})

    newTransFlat.groupBy(_._1).mapValues(l => l map (_._2))
  }


  // It returns a new SymbAFA2 where all transitions are disjoint. (It does not side effects the original automaton.)
  private def toSymbDisjointAFA2(safa: SymbAFA2): SymbAFA2 = {
    SymbAFA2(safa.initialStates, safa.finalStates, toSymbDisjointTrans(safa.transitions).asInstanceOf[Map[Int, Seq[SymbTransition]]])
  }

}


class SymbToConcTranslator(_safa: SymbAFA2) {

  val safa = toSymbDisjointAFA2(_safa)
  AFA2PrintingUtils.printAutDotToFile(safa, "symbDisjointAFA2.dot")

  val rangeMap : Map[Range, Int] = {
    val trans : Set[Range] = safa.transitions.values.flatten.map(_.symbLabel).toSet
    trans.zipWithIndex.toMap
  }

  def forth(): AFA2 = {
    val newTrans = safa.transitions.map{case (st, trSeq) =>
      (st, trSeq.map(x => StepTransition(rangeMap.get(x.symbLabel).get, x.step, x._targets)) )}

    AFA2(safa.initialStates, safa.finalStates, newTrans)
  }


  def back(afa: AFA2): SymbAFA2 = {
    val invMap = rangeMap.map(_.swap)
    val newTrans = afa.transitions.map{case (st, trSeq) =>
      (st, trSeq.map(x => SymbTransition(invMap.get(x.label).get, x.step, x._targets))) }

    SymbAFA2(afa.initialStates, afa.finalStates, newTrans)
  }

}
