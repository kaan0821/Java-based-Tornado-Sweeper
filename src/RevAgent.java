import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.Queue;

import java.util.Iterator;

import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;
import org.logicng.io.parsers.ParserException;
import org.logicng.io.parsers.PropositionalParser;
import org.logicng.io.parsers.ParserException;
import org.logicng.solvers.MiniSat;
import org.logicng.solvers.SATSolver;
import org.logicng.datastructures.Tristate;

public class RevAgent {

    //Stores the cells that are equivlaent to '0's in normal Tornado Sweeper
    private ArrayList<ArrayList<Integer>> zeroCells = new ArrayList<ArrayList<Integer>>();
    //Board from the agent's view
    private char[][] board;
    //Stores whether each cell has been probed or not
    private boolean[][] uncovered;
    //The actual game, to interact with
    private Game game;
    //A FIFO queue that that stores all the coords to realize looping on covered cells
    private Queue<ArrayList<Integer>> frontier = new LinkedList<ArrayList<Integer>>();;
    
    //Constructor of Agent
    public RevAgent(int row, int col, Game game) {

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
                this.frontier.add(temp);
            }
        }
    }

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
            String KB = makeKB();
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
                    if (Character.getNumericValue(this.game.getInfo(x, y)) == countNeighbor(x, y)) {
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
    public String makeKB() {
        //Knowledge Base
        StringBuilder KB = new StringBuilder();

        //Iterate over all uncovered numbered cells
        for (int i = 0; i < board.length; i++) {
            for (int j = 0; j < board[0].length; j++) {
                ArrayList<Integer> temp = new ArrayList<Integer>();
                temp.add(i);
                temp.add(j);
                if (uncovered[i][j] && !zeroCells.contains(temp) && board[i][j]!="*".charAt(0)) {
                    //Get the covered neighbors of the current cell
                    ArrayList<ArrayList<Integer>> neighbors = getNeighbors(i, j);
                    if (neighbors.size()>0) {
                        //A list that stores the clauses for the current cell
                        ArrayList<String> clauses = new ArrayList<String>();
                        int countNeighbor = countNeighbor(i, j);
                        //Translate the cell value to the normal Tornado Sweeper value
                        clauses.add(makeDNFClause(neighbors,countNeighbor-Character.getNumericValue(board[i][j])-countDanger(i, j)));
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
            return false;
          }
    }

    //If all cells have been uncovered or marked, win
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

    //Counts the number of neighbors
    public int countNeighbor(int x, int y) {
        int count = 0;
        for (int i = x-1; i <= x+1; i++) {
            for (int j = y-1; j <= y+1; j++) {
                if (i >= 0 && i < board.length && j >= 0 && j < board[0].length
                && !(i == x-1 && j == y+1) && !(i==x+1 && j==y-1)) {
                    count ++;   
                }
            }
        }
        count --;
        return count;
    }

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

    //Probing all the neighbors if a 0-equivalent cell is discovered
    public void probeNeighbors(int x, int y) {
        for (int i = x-1; i <= x+1; i++) {
            for (int j = y-1; j <= y+1; j++) {
                if (i >= 0 && i < board.length && j >= 0 && j < board[0].length && !uncovered[i][j]
                && !(i == x-1 && j == y+1) && !(i==x+1 && j==y-1)) {
                    char cellValue = this.game.getInfo(i, j);
                    uncovered[i][j] = true;
                    board[i][j] = cellValue;
                    //If 0-equavalent, keep probing
                    if (cellValue == countNeighbor(i, j)) {
                        ArrayList<Integer> temp = new ArrayList<Integer>();
                        temp.add(i);
                        temp.add(j);
                        zeroCells.add(temp);
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
        //Probe the first cell, if 0-equivalent probe all 0-equivalents
        if (Character.getNumericValue(val) == countNeighbor(0, 0)) {
            this.board[0][0] = val;
            ArrayList<Integer> temp = new ArrayList<Integer>();
            temp.add(0);
            temp.add(0);
            zeroCells.add(temp);
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
            if (Character.getNumericValue(val) == countNeighbor(hint2, hint2)) {
                ArrayList<Integer> temp2 = new ArrayList<Integer>();
                temp2.add(0);
                temp2.add(0);
                zeroCells.add(temp2);
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
