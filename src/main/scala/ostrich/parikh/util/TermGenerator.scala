package ostrich.parikh

import ap.parser.ITerm
import ap.terfor.ConstantTerm
import ap.terfor.TermOrder
import ap.parser.IExpression._

object TermGeneratorOrder {
  ParikhUtil.todo("no global variable")
  def reset() = {
    order = TermOrder.EMPTY
  }
  implicit var order: TermOrder = TermOrder.EMPTY

  def apply(): TermOrder = order

  def extend(t: ConstantTerm): Unit = {
    if(!order.orderedConstants.contains(t))
      order = order.extend(t)
  }
  def extend(otherOrder: TermOrder): Unit = {
    val newConsts = otherOrder.orderedConstants &~ order.orderedConstants 
    val newPreds = otherOrder.orderedPredicates &~ order.orderedPredicates 
    order = order.extend(otherOrder.sort(newConsts))
    order = order.extendPred(otherOrder.sortPreds(newPreds))
  }
}

object RegisterTerm {
  var count = 0
  def apply(): ITerm = {
    count += 1
    val regTerm = Sort.Integer.newConstant(s"R$count")
    TermGeneratorOrder.extend(regTerm)
    regTerm
  }
}

object TransitionTerm {
  var count = 0
  def apply(): ITerm = {
    count += 1
    val transTerm = new ConstantTerm(s"T$count")
    TermGeneratorOrder.extend(transTerm)
    transTerm
  }
}

object ZTerm {
  var count = 0
  def apply(): ITerm = {
    count += 1
    val zTerm = new ConstantTerm(s"Z$count")
    TermGeneratorOrder.extend(zTerm)
    zTerm
  }
}

object LenTerm {
  var count = 0
  def apply(): ITerm = {
    count += 1
    val lenTerm = new ConstantTerm(s"Len$count")
    TermGeneratorOrder.extend(lenTerm)
    lenTerm
  }
}

object IntTerm {
  var count = 0
  def apply(): ITerm = {
    count += 1
    val lenTerm = new ConstantTerm(s"Int$count")
    TermGeneratorOrder.extend(lenTerm)
    lenTerm
  }
}