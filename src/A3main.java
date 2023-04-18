
import java.util.ArrayList;


public class A3main {

	public static void main(String[] args) {
		
		boolean verbose=false; //prints the formulas for SAT if true
		if (args.length>2 && args[2].equals("verbose") ){
			verbose=true; //prints the formulas for SAT if true
		}

		// read input from command line
		// Agent type
		System.out.println("-------------------------------------------\n");
		System.out.println("Agent " + args[0] + " plays " + args[1] + "\n");

		// World
		World world = World.valueOf(args[1]);
		char[][] p = world.map;
		printBoard(p);
		System.out.println("Start!");

		//Creating the game and the agent
		int row = world.map.length;
		int col = world.map[0].length;
		Game game = new Game(world.map);
		Agent agent = new Agent(row, col , game);

		switch (args[0]) {
			case "P1":
				//Method returns boolean to indicate whether win or lose
				boolean win = agent.orderProbe(verbose);
				System.out.println("Final map");
				printBoard(agent.getBoard());
				if (!win) {
					System.out.println("\nResult: Agent dead: found mine\n");
				} else {
					System.out.println("\nResult: Agent alive: all solved\n");
				}
			case "P2":
			if (args[0].equals("P2")){
				//Method returns boolean to indicate whether win or stuck
				boolean win2 = agent.spsProbe(verbose);
				System.out.println("Final map");
				printBoard(agent.getBoard());
				if (win2) {
					System.out.println("\nResult: Agent alive: all solved\n");
				} else {
					System.out.println("\nResult: Agent not terminated\n");
				}
			}
			case "P3":
			if (args[0].equals("P3")) {
				//Method returns boolean to indicate whether win or stuck
				boolean win3 = agent.dnfSatProbe(verbose);
				System.out.println("Final map");
				printBoard(agent.getBoard());
				if (win3) {
					System.out.println("\nResult: Agent alive: all solved\n");
				} else {
					System.out.println("\nResult: Agent not terminated\n");
				}
			}
			case "P4":
			if (args[0].equals("P4")) {
				//Method returns boolean to indicate whether win or stuck
				boolean win4 = agent.cnfSatProbe(verbose);
				System.out.println("Final map");
				printBoard(agent.getBoard());
				if (win4) {
					System.out.println("\nResult: Agent alive: all solved\n");
				} else {
					System.out.println("\nResult: Agent not terminated\n");
				}
			}
			//To play reverse Tornado Sweeper, DNF probing is used as default
			case "P5":
			if (args[0].equals("P5")) {
				RevAgent revAgent = new RevAgent(row, col , game);
				//Method returns boolean to indicate whether win or stuck
				boolean win5 = revAgent.dnfSatProbe(verbose);
				System.out.println("Final map");
				printBoard(revAgent.getBoard());
				if (win5) {
					System.out.println("\nResult: Agent alive: all solved\n");
				} else {
					System.out.println("\nResult: Agent not terminated\n");
				}
			}

		}


		//templates to print results - copy to appropriate places
		//System.out.println("\nResult: Agent alive: all solved\n");
		//System.out.println("\nResult: Agent dead: found mine\n");
		//System.out.println("\nResult: Agent not terminated\n");

	}

	
	//prints the board in the required format - PLEASE DO NOT MODIFY
	public static void printBoard(char[][] board) {
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
