import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.Queue;

import java.util.Iterator;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;
import org.logicng.io.parsers.ParserException;
import org.logicng.io.parsers.PropositionalParser;
import org.logicng.io.parsers.ParserException;
import org.logicng.solvers.MiniSat;
import org.logicng.solvers.SATSolver;
import org.logicng.datastructures.Tristate;

public class Agent {

    //Stores all the cells that are still covered for Part1 mainly
    private ArrayList<ArrayList<Integer>> coveredCells = new ArrayList<ArrayList<Integer>>();
    //Board from the agent's view
    private char[][] board;
    //Stores whether each cell has been probed or not
    private boolean[][] uncovered;
    //The actual game, to interact with
    private Game game;
    //A FIFO queue that that stores all the coords to realize looping on covered cells
    private Queue<ArrayList<Integer>> frontier = new LinkedList<ArrayList<Integer>>();;
    
    //Constructor of Agent
    public Agent(int row, int col, Game game) {

        //The actual game board
        this.game = game;
        char[][] board = new char[row][col];
        this.uncovered = new boolean[row][col];
        //Initialize a brand new board
        for (int i = 0; i < row; i++) {
            for (int j = 0; j < col; j++) {
                board[i][j] = "?".charAt(0);
            }
        }
        this.board = board;

        // initialize uncoveredCells & frontier list with all coordinates
        for (int i = 0; i < board.length; i++) {
            for (int j = 0; j < board[i].length; j++) {
                ArrayList<Integer> temp = new ArrayList<Integer>();
                temp.add(i);
                temp.add(j);
                this.coveredCells.add(temp);
                this.frontier.add(temp);
            }
        }
    }

/** ---------------------------   Part 4 ------------------------------*/
    //SAT probing using CNF
    public boolean cnfSatProbe(boolean verbose) {
        if (verbose) {printSelf();}
        //Probing the given two cells first
        initialProbe(verbose);
        //This list stores cells that nothing can be done with them
        ArrayList<ArrayList<Integer>> trace = new ArrayList<ArrayList<Integer>>();
        //Initialize a count to check for stalemate situation
        int count = 0;

        //Probing starts
        while (!frontier.isEmpty()) {
            //Each iteration, first check if already won
            if (checkActualWin()) {
                return true;
            }
            //For each iteration, consturct the current knowledge base of the world
            String KB = makeKB("cnf");
            //System.out.println(KB);
            ArrayList<Integer> coord = frontier.poll();

            //Check for stuck situation
            if (trace.contains(coord)) {
                if (count == trace.size()) {
                    return false;
                }
            }
            int x = coord.get(0);
            int y = coord.get(1);
            //If it's a covered cell
            if (uncovered[x][y] == false) {
                String Dclause = "&(~D"+ Integer.toString(x)+Integer.toString(y)+")";
                String Pclause = "&(D"+ Integer.toString(x)+Integer.toString(y)+")";
                try {
                    //Check the cell in question is a danger with logicng
                    boolean ifDanger = satDelegate(KB+Dclause);
                    //Check the cell in question is safe with logicng
                    boolean ifProbe = satDelegate(KB+Pclause);
                    //If safe, probe
                    if (ifProbe) {
                        uncovered[x][y] = true;
                        if (this.game.getInfo(x, y) == '0') {
                            this.board[x][y] = this.game.getInfo(x, y);
                            probeNeighbors(x, y);
                            //Remove from trace and reset count
                            if (trace.contains(coord)) {
                                trace.remove(coord);
                                count = 0;
                            }
                        } else {
                            board[x][y] = this.game.getInfo(x, y);
                            if (trace.contains(coord)) {
                                trace.remove(coord);
                                count = 0;
                            }
                        }
                        if (verbose) {printSelf();}
                //If danger, mark it as danger
                    } else if (ifDanger) {
                        uncovered[x][y] = true;
                        board[x][y] = "*".charAt(0);
                        //Remove from trace and reset count
                        if (trace.contains(coord)) {
                            trace.remove(coord);
                            count = 0;
                        }
                        if (verbose) {printSelf();}
                //No candidates, nothing can be done, add to back of the queue
                //Add to trace if not yet, increment count if already in trace
                    } else {
                        frontier.add(coord);
                        if (!trace.contains(coord)) {
                            trace.add(coord);
                        } else {
                            count ++;
                        }
                    }
                } catch (Error e) {
                    return false;
                }
                
            }
        }
        return true;
    }

    //Need this delegate to capture Contradiction Exception, cuz it indicates unsatisfiable
    public boolean satDelegate(String query) {
        try {
            boolean result = sat4j(query);
            if (result) {
                return true;
            } else {
                return false;
            }
        } catch (ContradictionException e) {
            return true;
        } catch (TimeoutException e) {
            return false;
        }

    }

    //Construct each CNF clause, count indicates how many dangers are in the neighbors
    public String makeCNFClause(ArrayList<ArrayList<Integer>> neighbors, int count) {
        String clause = "";
        
        //Basically AFN, no need to go through atMost and atLeast
        if (count == 0) {
            for (int i = 0;i<neighbors.size();i++) {
                int row = neighbors.get(i).get(0);
                int col = neighbors.get(i).get(1);
                clause += "~D" + Integer.toString(row) + Integer.toString(col)+"&";
            }
            clause = clause.substring(0,clause.length()-1);
        //First construct atMost then atLeast then combine
        } else if (neighbors.size() != count) {
            String mostClause = atMost(neighbors, count);
            String leastClause = atMostNon(neighbors, neighbors.size()-count);
            clause = mostClause + leastClause;
        //If AMN, all dangers nearby
        } else {
            for (int i = 0;i<neighbors.size();i++) {
                int row = neighbors.get(i).get(0);
                int col = neighbors.get(i).get(1);
                clause += "D" + Integer.toString(row) + Integer.toString(col)+"&";
            }
            clause = clause.substring(0,clause.length()-1);
        }

        return clause.toString();
    
    }

    //Constructs the logic sentence for at most n dangers in neighbors
    public String atMost(ArrayList<ArrayList<Integer>> neighbors, int count) {

        StringBuilder clause = new StringBuilder();
    
        // Generate the clause
        // The loop iterates over all possible subsets of the neighbors
        // i has n bits and each bit indicates whether the literal is included or not. 2^n combinations
        int n = neighbors.size();
        if (n == 1) {
            ArrayList<Integer> coords = neighbors.get(0);
            int row = coords.get(0);
            int col = coords.get(1);
            clause.append("~D" + row + col + "&");
        } else {
            for (int i = 0; i < (1 << n); i++) {
                //'1' in the i indicates Dij, 0 indicates ~Dij
                int setBits = Integer.bitCount(i);
                if (setBits == count + 1) {
                    clause.append("(");
                    boolean firstLiteral = true;
                    for (int j = 0; j < n; j++) {
                        if (((i >> j) & 1) == 1) {
                            if (!firstLiteral) {
                                clause.append("|");
                            } else {
                                firstLiteral = false;
                            }
                            ArrayList<Integer> coords = neighbors.get(j);
                            int row = coords.get(0);
                            int col = coords.get(1);
                            clause.append("~D" + row + col);
                        }
                    }
                    clause.append(")&");
                }
            }
        }
        return clause.toString();
    }

    //Constructs the logic sentence for at least n dangers in neighbors
    //Basically at most neighbors-count non-danger neighbors
    public String atMostNon(ArrayList<ArrayList<Integer>> neighbors, int count) {

        StringBuilder clause = new StringBuilder();
    
        // Generate the clause
        // The loop iterates over all possible subsets of the neighbors
        // i has n bits and each bit indicates whether the literal is included or not. 2^n combinations
        int n = neighbors.size();
        for (int i = 0; i < (1 << n); i++) {
            //'1' in the i indicates ~Dij, 0 indicates Dij
            int setBits = Integer.bitCount(i);
            if (setBits == count + 1) {
                clause.append("(");
                boolean firstLiteral = true;
                for (int j = 0; j < n; j++) {
                    if (((i >> j) & 1) == 1) {
                        if (!firstLiteral) {
                            clause.append("|");
                        } else {
                            firstLiteral = false;
                        }
                        ArrayList<Integer> coords = neighbors.get(j);
                        int row = coords.get(0);
                        int col = coords.get(1);
                        clause.append("D" + row + col);
                    }
                }
                clause.append(")&");
            }
        }
    
        // Remove the last redundant character
        if (clause.length() > 0) {
            clause.deleteCharAt(clause.length() - 1);
        }
    
        return clause.toString();
    }


    //Sat4j solver for Part 4
    public boolean sat4j(String query) throws ContradictionException, TimeoutException {
        //Remove the D's and parentheses and split the query by "&"
        query = query.replaceAll("D", "");
        String[] clauseStrings = query.replaceAll("[()]", "").split("&");
        int nbClauses = clauseStrings.length;
        //Prepare the Sat4j solver
        ISolver solver = SolverFactory.newDefault();
        //Make sure we can store a lot of variables
        solver.newVar(10000);
        solver.setExpectedNumberOfClauses(nbClauses);

        // convert each clause to DIMACS form and add to the solver
        for (String clauseString : clauseStrings) {
            if (clauseString != "") {
                String[] literals = clauseString.trim().split("\\|");
                int[] dimacsClause = new int[literals.length];
                for (int i = 0; i < literals.length; i++) {
                    String literal = literals[i].trim();
                    if (literal.charAt(0) == '~') {
                        //Directly encode them by their coordinates
                        dimacsClause[i] = -1 * Integer.parseInt(literal.substring(1));
                    } else {
                        dimacsClause[i] = Integer.parseInt(literal);
                    }
                }
                solver.addClause(new VecInt(dimacsClause));
            }
        }

        //Check if the problem is satisfiable
        //If throws ContradictionException, it's also unsatisfiable
        IProblem problem = solver;
        if (!problem.isSatisfiable()) {
            return true;
        } else {
            return false;
        }

    }
/** ---------------------------   Part 3 ------------------------------*/
    //SAT probing using DNF
    public boolean dnfSatProbe(boolean verbose) {
        if (verbose) {printSelf();}
        //Probing the given two cells first
        initialProbe(verbose);

        //This list stores cells that nothing can be done with them
        ArrayList<ArrayList<Integer>> trace = new ArrayList<ArrayList<Integer>>();
        //Initialize a count to check for stalemate situation
        int count = 0;
         //Probing starts
         while (!frontier.isEmpty()) {
            //Each iteration, first check if already won
            if (checkActualWin()) {
                return true;
            }
            //For each iteration, consturct the current knowledge base of the world
            String KB = makeKB("dnf");
            ArrayList<Integer> coord = frontier.poll();

            //Check for stuck situation
            if (trace.contains(coord)) {
                if (count == trace.size()) {
                    return false;
                }
            }
            int x = coord.get(0);
            int y = coord.get(1);
            //If it's a covered cell
            if (uncovered[x][y] == false) {
                String Dclause;
                String Pclause;
                //This happens only if all the outter cells are tornadoes
                if (KB.length() == 0) {
                    Dclause = "(~D"+ Integer.toString(x)+Integer.toString(y)+")";
                    Pclause = "(D"+ Integer.toString(x)+Integer.toString(y)+")";
                } else {
                    Dclause = "&(~D"+ Integer.toString(x)+Integer.toString(y)+")";
                    Pclause = "&(D"+ Integer.toString(x)+Integer.toString(y)+")";
                }
                //Check the cell in question is a danger with logicng
                boolean ifDanger = logicng(KB+Dclause);
                //Check the cell in question is safe with logicng
                boolean ifProbe = logicng(KB+Pclause);
                //If safe, probe
                if (ifProbe) {
                    uncovered[x][y] = true;
                    if (this.game.getInfo(x, y) == '0') {
                        this.board[x][y] = this.game.getInfo(x, y);
                        probeNeighbors(x, y);
                        //Remove from trace and reset count
                        if (trace.contains(coord)) {
                            trace.remove(coord);
                            count = 0;
                        }
                    } else {
                        board[x][y] = this.game.getInfo(x, y);
                        if (trace.contains(coord)) {
                            trace.remove(coord);
                            count = 0;
                        }
                    }
                    if (verbose) {printSelf();}
            //If danger, mark it as danger
                } else if (ifDanger) {
                    uncovered[x][y] = true;
                    board[x][y] = "*".charAt(0);
                    //Remove from trace and reset count
                    if (trace.contains(coord)) {
                        trace.remove(coord);
                        count = 0;
                    }
                    if (verbose) {printSelf();}
            //No candidates, nothing can be done, add to back of the queue
            //Add to trace if not yet, increment count if already in trace
                } else {
                    frontier.add(coord);
                    if (!trace.contains(coord)) {
                        trace.add(coord);
                    } else {
                        count ++;
                    }
                }
            }
        }
        return true;
    }

    //Constructing the knowledge base query in DNF
    public String makeKB(String encoding) {
        //Knowledge Base
        StringBuilder KB = new StringBuilder();

        //Iterate over all uncovered numbered cells
        for (int i = 0; i < board.length; i++) {
            for (int j = 0; j < board[0].length; j++) {
                if (uncovered[i][j] && board[i][j] != "0".charAt(0) && board[i][j]!="*".charAt(0)) {
                    //Get the covered neighbors of the current cell
                    ArrayList<ArrayList<Integer>> neighbors = getNeighbors(i, j);
                    if (neighbors.size()>0) {
                        //A list that stores the clauses for the current cell
                        ArrayList<String> clauses = new ArrayList<String>();
                        if (encoding.equals("dnf")) {
                            clauses.add(makeDNFClause(neighbors,Character.getNumericValue(board[i][j])-countDanger(i, j)));
                        } else {
                            clauses.add(makeCNFClause(neighbors,Character.getNumericValue(board[i][j])-countDanger(i, j)));
                        }
                        for (String each : clauses) {
                            KB.append(each +"&");
                        }
                    }
                    
                }
            }
        }
        //Stripe the ending &
        if (KB.length() != 0) {
            KB.deleteCharAt(KB.length()-1);
        }
        return KB.toString();

    }

    //Construct each DNF clause, count indicates how many dangers are in the neighbors
    public String makeDNFClause(ArrayList<ArrayList<Integer>> neighbors, int count) {
        
        StringBuilder clause = new StringBuilder();
        if (neighbors.size() != 1) {
            clause.append("(");
        }
        int n = neighbors.size();
        String[] literals = new String[n];
    
        //Construct the literal representation for each neighbor
        for (int i = 0; i < n; i++) {
            ArrayList<Integer> coords = neighbors.get(i);
            int row = coords.get(0);
            int col = coords.get(1);
            literals[i] = "D" + row + col;
        }
    
        //Generate the clause
        //The loop iterates over all possible subsets of the neighbors
        //i has n bits and each bit indicates whether the literal is included or not. 2^n combinations
        for (int i = 0; i < (1 << n); i++) {
            //'1' in the i indicates Dij, 0 indicates ~Dij
            int setBits = Integer.bitCount(i);
            //Counts the '1' in the i, if the 'count' number of '1' is included, make the clause
            if (setBits == count) {
                clause.append("(");
                for (int j = 0; j < n; j++) {
                    if (((i >> j) & 1) == 1) {
                        clause.append(literals[j]).append("&");
                    } else {
                        clause.append("~").append(literals[j]).append("&");
                    }
                }
                clause.setCharAt(clause.length() - 1, ')');
                clause.append("|");
            }
        }
    
        //Remove the trailing char and close the clause
        if (neighbors.size() == 1) {
            clause.setLength(clause.length() - 1);
        } else {
            clause.setCharAt(clause.length() - 1, ')');
        }
        return clause.toString();
    }

    //LogicNG SAT solver for Part 3
    public boolean logicng(String query) {
        try{

            FormulaFactory f = new FormulaFactory();
            PropositionalParser p = new PropositionalParser(f);
            
            Formula formula = p.parse(query);
            
            SATSolver miniSat = MiniSat.miniSat(f);
            miniSat.add(formula);
            Tristate result = miniSat.sat();
            if (result == Tristate.FALSE) {
                return true;
            } else {
                return false;
            }
      
          } catch (ParserException e) {
            System.out.println("Error");
            e.printStackTrace();
            return false;
          }
    }

/** ---------------------------   Part 2 ------------------------------*/
    //SPS Strategy probe
    public boolean spsProbe(boolean verbose) {
        if (verbose) {printSelf();}
        //Probing the given two cells first
        initialProbe(verbose);
        //This list stores cells that are neither AMN nor AFN, nothing can be done with it
        ArrayList<ArrayList<Integer>> trace = new ArrayList<ArrayList<Integer>>();
        //Initialize a count to check for stalemate situation
        int count = 0;
        //SPS Probing starts
        while (!frontier.isEmpty()) {
            //Each iteration, first check if already won
            if (checkActualWin()) {
                return true;
            }

            ArrayList<Integer> coord = frontier.poll();
            //Count increments everytime it meets a previously difficult cell
            //It is set to zero everytime a cell in trace is newly dealt with
            //If all that's left are the cells where nothing can be done with
            //the count will equal the size of trace, cuz none of them can be further dealt with
            //Now we have a stalemate
            if (trace.contains(coord)) {
                if (count == trace.size()) {
                    return false;
                }
            }
            int x = coord.get(0);
            int y = coord.get(1);
            //If it's a covered cell
            if (uncovered[x][y] == false) {
                //If AFN, reveal it
                if (AFN(x,y)) {
                    uncovered[x][y] = true;
                    if (this.game.getInfo(x, y) == '0') {
                        this.board[x][y] = this.game.getInfo(x, y);
                        probeNeighbors(x, y);
                        //Remove from trace and reset count
                        if (trace.contains(coord)) {
                            trace.remove(coord);
                            count = 0;
                        }
                    } else {
                        board[x][y] = this.game.getInfo(x, y);
                        if (trace.contains(coord)) {
                            trace.remove(coord);
                            count = 0;
                        }
                    }
                    if (verbose) {printSelf();}
            //If AMN, mark it as danger
                } else if (AMN(x,y)) {
                    uncovered[x][y] = true;
                    board[x][y] = "*".charAt(0);
                    //Remove from trace and reset count
                    if (trace.contains(coord)) {
                        trace.remove(coord);
                        count = 0;
                    }
                    if (verbose) {printSelf();}
            //No candidates, nothing can be done, add to back of the queue
            //Add to trace if not yet, increment count if already in trace
                } else {
                    frontier.add(coord);
                    if (!trace.contains(coord)) {
                        trace.add(coord);
                    } else {
                        count ++;
                    }
                }
            }
        }
        return true;
    }



    //Check if AMN situation
    public boolean AMN(int x, int y) {
        //For each uncovered neighbor
        for (int i = x-1; i <= x+1; i++) {
            for (int j = y-1; j <= y+1; j++) {
                if (i >= 0 && i < board.length && j >= 0 && j < board[0].length
                && !(i == x-1 && j == y+1) && !(i==x+1 && j==y-1)) {
                    if (uncovered[i][j] == true) {
                        //if #covered = #clue - #marked danger, AMN
                        if (countCovered(i, j) == Character.getNumericValue(board[i][j]) - countDanger(i, j)) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    //Check if win for Part2 onwards
    //If all cells have been uncovered or marked, check if board same
    public boolean checkActualWin() {
        for (int i = 0; i < uncovered.length;i++) {
            for (int j = 0; j<uncovered[0].length;j++) {
                if (uncovered[i][j] == false) {
                    return false;
                }
            }
        }
        if (game.ifWin(board)) {
            return true;
        }
        return false;
    }

    //Check if AFN situation
    public boolean AFN(int x, int y) {
        //For each uncovered neighbor
        for (int i = x-1; i <= x+1; i++) {
            for (int j = y-1; j <= y+1; j++) {
                if (i >= 0 && i < board.length && j >= 0 && j < board[0].length
                && !(i == x-1 && j == y+1) && !(i==x+1 && j==y-1)) {
                    if (uncovered[i][j] == true) {
                        ////if #clue = #marked danger, AFN
                        if (Character.getNumericValue(board[i][j]) == countDanger(i, j)) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    //Counts the number of marked neighbor dangers
    public int countDanger(int x, int y) {
        int count = 0;
        for (int i = x-1; i <= x+1; i++) {
            for (int j = y-1; j <= y+1; j++) {
                if (i >= 0 && i < board.length && j >= 0 && j < board[0].length
                && !(i == x-1 && j == y+1) && !(i==x+1 && j==y-1)) {
                    if (board[i][j] == "*".charAt(0)) {
                        count ++;
                    }
                    
                }
            }
        }
        return count;
    }

    //Counts the number of covered cells
    public int countCovered(int x, int y) {
        int count = 0;
        for (int i = x-1; i <= x+1; i++) {
            for (int j = y-1; j <= y+1; j++) {
                if (i >= 0 && i < board.length && j >= 0 && j < board[0].length
                && !(i == x-1 && j == y+1) && !(i==x+1 && j==y-1)) {
                    if (uncovered[i][j] == false) {
                        count ++;
                    }
                    
                }
            }
        }
        return count;
    }

/** ---------------------------   Part 1 ------------------------------*/
    //Probing cells in order for Part 1
    public boolean orderProbe(boolean verbose) {
        if (verbose) {printSelf();}
        while (!coveredCells.isEmpty()) {
            //Check if won at every iteration
            if (checkWin()) {
                return true;
            }
            //Simply remove the head from the array each time
            ArrayList<Integer> coord = coveredCells.remove(0);
            int x = coord.get(0);
            int y = coord.get(1);
            if (uncovered[x][y] == false) {
                uncovered[x][y] = true;
                char val = this.game.getInfo(x, y);
                //If probed a danger, immediately lose
                if (val == 't') {
                    this.board[x][y] = "-".charAt(0);
                    return false;
                //If probed a 0, probe all 0's nearby
                } else if (val == '0') {
                    this.board[x][y] = val;
                    probeNeighbors(x, y);
                    //In case accidentally win
                    if (checkWin()) {
                        return true;
                    }
                    if (verbose) {printSelf();}
                //Simply reveal if just a normal cell
                } else {
                    this.board[x][y] = val;
                    if (verbose) {printSelf();}
                }
            }
        }
        return true;

    }

    //Check if the game wins for Part 1
    public boolean checkWin() {
        int count = 0;
        for (int i=0; i<uncovered.length;i++) {
            for (int j=0; j<uncovered[0].length;j++) {
                if (uncovered[i][j] == false) {
                    count++;
                }
            }
        }
        //If only one cell is covered, that must be the tornado, hence win
        if (count == 1) {
            return true;
        } else {
            return false;
        }
    }

/** ---------------------------   General Utility ------------------------------*/
    //Getting all the covered/flagged neighbors' coordinates
    public ArrayList<ArrayList<Integer>> getNeighbors(int x, int y) {
        //Stores the eventual list of covered neighbor coordinates
        ArrayList<ArrayList<Integer>> neighbors = new ArrayList<ArrayList<Integer>>();
        for (int i = x-1; i <= x+1; i++) {
            for (int j = y-1; j <= y+1; j++) {
                if (i >= 0 && i < board.length && j >= 0 && j < board[0].length && !uncovered[i][j]
                && !(i == x-1 && j == y+1) && !(i==x+1 && j==y-1)) {
                    ArrayList<Integer> temp = new ArrayList<Integer>();
                    temp.add(i);
                    temp.add(j);
                    neighbors.add(temp);
                }
            }
        }
        return neighbors;
    }

    //Probing all the neighbors if 0 is discovered
    public void probeNeighbors(int x, int y) {
        for (int i = x-1; i <= x+1; i++) {
            for (int j = y-1; j <= y+1; j++) {
                if (i >= 0 && i < board.length && j >= 0 && j < board[0].length && !uncovered[i][j]
                && !(i == x-1 && j == y+1) && !(i==x+1 && j==y-1)) {
                    char cellValue = this.game.getInfo(i, j);
                    uncovered[i][j] = true;
                    board[i][j] = cellValue;
                    if (cellValue == '0') {
                        probeNeighbors(i, j);
                    }
                }
            }
        }
    }

    //Return the current board
    public char[][] getBoard() {
        return this.board;
    }

    //Probing the initial two hinted cells
    public void initialProbe(boolean verbose) {
        //Middle cell
        int hint2 = board.length/2;
        //Getting value from the game class
        char val = this.game.getInfo(0, 0);
        uncovered[0][0] = true;
        //Probe the first cell, if 0 probe all 0's
        if (val == '0') {
            this.board[0][0] = val;
            probeNeighbors(0, 0);
            if (verbose) {printSelf();}
        //If not 0, simply probe
        } else {
            this.board[0][0] = val;
            if (verbose) {printSelf();}
        }
        //Probe the middle cell, same process
        if (uncovered[hint2][hint2]==false) {
            val = this.game.getInfo(hint2, hint2);
            uncovered[hint2][hint2] = true;
            if (val == '0') {
                this.board[hint2][hint2] = val;
                probeNeighbors(hint2, hint2);
                if (verbose) {printSelf();}
            } else {
                this.board[hint2][hint2] = val;
                if (verbose) {printSelf();}
            }
        }
    }

    //Prints the current board 
	public void printSelf() {
		System.out.println();
		// first line
		for (int l = 0; l < board.length + 5; l++) {
			System.out.print(" ");// shift to start
		}
		for (int j = 0; j < board[0].length; j++) {
			System.out.print(j);// x indexes
			if (j < 10) {
				System.out.print(" ");
			}
		}
		System.out.println();
		// second line
		for (int l = 0; l < board.length + 3; l++) {
			System.out.print(" ");
		}
		for (int j = 0; j < board[0].length; j++) {
			System.out.print(" -");// separator
		}
		System.out.println();
		// the board
		for (int i = 0; i < board.length; i++) {
			for (int l = i; l < board.length - 1; l++) {
				System.out.print(" ");// fill with left-hand spaces
			}
			if (i < 10) {
				System.out.print(" ");
			}

			System.out.print(i + "/ ");// index+separator
			for (int j = 0; j < board[0].length; j++) {
				System.out.print(board[i][j] + " ");// value in the board
			}
			System.out.println();
		}
		System.out.println();
	}
}
