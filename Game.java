import java.util.ArrayList;

public class Game {
    
    private char[][] board;
    
    //Constructor -- 
    public Game(char[][] board) {
        this.board = board;
    }

    //Reveal the information on the specific cell
    public char getInfo(int row, int col) {
        return this.board[row][col];
    }
    
    //Return the game board
    public char[][] getBoard() {
        return this.board;
    }


    //If a tornado is uncovered, lose immediately
    public boolean ifLose(int row, int col) {
        if (this.board[row][col] == "t".charAt(0)) {
            return true;
        }
        return false;
    }

    //Check if the result board is the same as actual board
    public boolean ifWin(char[][] currBoard) {
        //First change all the * to t
        char[][] temp = new char[this.board.length][this.board[0].length];
        for (int i = 0; i < this.board.length;i++) {
            for (int j = 0; j<this.board[0].length;j++) {
                if (currBoard[i][j]=='*') {
                    temp[i][j] = 't';
                } else {
                    temp[i][j] = currBoard[i][j];
                }
            }
        }
        for (int i = 0; i < this.board.length;i++) {
            for (int j = 0; j<this.board[0].length;j++) {
                if (temp[i][j] != this.board[i][j]) {
                    return false;
                }
            }
        }
        return true;
    }
}
