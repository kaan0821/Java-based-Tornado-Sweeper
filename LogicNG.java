
import java.util.Iterator;

import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;
import org.logicng.io.parsers.ParserException;
import org.logicng.io.parsers.PropositionalParser;
import org.logicng.io.parsers.ParserException;
import org.logicng.solvers.MiniSat;
import org.logicng.solvers.SATSolver;
import org.logicng.datastructures.Tristate;

/*
 * Notation
 *
 * &: AND
 * |: OR
 * ~: NOT
 * =>: IMP
 * <=>: EQUIV
 */
public class LogicNG {

  private static Tristate result;
  public static void main(String query){

    try{
        
      FormulaFactory f = new FormulaFactory();
      PropositionalParser p = new PropositionalParser(f);
      
      Formula formula = p.parse(query);
      
      SATSolver miniSat=MiniSat.miniSat(f);
      miniSat.add(formula);
      result=miniSat.sat();

    } catch (ParserException e) {
      e.printStackTrace();
    }
  }

  public boolean getResult() {
    if (result.equals("FALSE")) {
        return false;
    } else {
        return true;
    }
  }
}
