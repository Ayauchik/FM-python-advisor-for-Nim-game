import functools
import tkinter as tk
from tkinter import ttk, scrolledtext
from typing import List

# --- Global Game State Management ---
current_heaps: List[int] = []

def calculate_nim_sum(heaps: List[int]) -> int:
    """Calculates the bitwise XOR (Nim-sum) of all heap sizes."""
    return functools.reduce(lambda x, y: x ^ y, heaps) if heaps else 0

class NimAdvisorApp:
    def __init__(self, master):
        self.master = master
        master.title("Normal Nim Game Tracker (Last Player WINS)")

        global current_heaps
        self.heaps = current_heaps
        self.turn_count = 0
        self.move_options = []

        # --- Configure Grid Layout ---
        master.columnconfigure(0, weight=1)
        master.rowconfigure(3, weight=1)

        # --- 1. Control Frame (Input, Status, Button) ---
        self.control_frame = ttk.Frame(master, padding="10")
        self.control_frame.grid(row=0, column=0, sticky="ew")

        # Initial Input (Start Game)
        ttk.Label(self.control_frame, text="Start Heaps (e.g., 5 6 7):").pack(side=tk.LEFT, padx=(0, 10))
        self.start_input = ttk.Entry(self.control_frame, width=20)
        self.start_input.pack(side=tk.LEFT, expand=True, fill='x')
        self.start_input.bind('<Return>', lambda event: self.start_new_game())
        
        ttk.Button(self.control_frame, text="Start Game", command=self.start_new_game).pack(side=tk.LEFT, padx=(10, 0))
        
        # --- 2. Status Display ---
        self.status_var = tk.StringVar(value="Start a new game to begin tracking moves.")
        self.status_label = ttk.Label(master, textvariable=self.status_var, font=('Helvetica', 10, 'bold'), padding="5")
        self.status_label.grid(row=1, column=0, sticky="ew")
        
        # --- 3. Move Selection Frame (Dynamically populated with buttons) ---
        self.move_frame = ttk.Frame(master, padding="10")
        self.move_frame.grid(row=2, column=0, sticky="w") # Changed sticky to 'w' for column layout
        ttk.Label(self.move_frame, text="Your Move Options:").grid(row=0, column=0, sticky="w", pady=(0, 5))
        
        # --- 4. Game Log (Scrolled Text Area) ---
        ttk.Label(master, text="Game Log / Strategy Trace:").grid(row=3, column=0, sticky="sw", padx=10, pady=(10, 0))
        
        # INCREASED HEIGHT HERE: height=25 (was 15)
        self.log_area = scrolledtext.ScrolledText(master, wrap=tk.WORD, width=70, height=25, font=('Courier', 10))
        self.log_area.grid(row=4, column=0, sticky="nsew", padx=10, pady=(0, 10))
        self.log_area.config(state=tk.DISABLED) # Disable editing

    # --- Logging Functions ---
    def log_move(self, text: str):
        """Helper to append text to the game log area."""
        self.log_area.config(state=tk.NORMAL)
        self.log_area.insert(tk.END, text + "\n")
        self.log_area.see(tk.END) # Scroll to the bottom
        self.log_area.config(state=tk.DISABLED)
        
    def clear_log(self):
        self.log_area.config(state=tk.NORMAL)
        self.log_area.delete('1.0', tk.END)
        self.log_area.config(state=tk.DISABLED)

    # --- Game Start ---
    def start_new_game(self):
        input_str = self.start_input.get().strip()
        try:
            new_heaps = [int(h.strip()) for h in input_str.split() if h.strip().isdigit()]
            new_heaps = [h for h in new_heaps if h > 0]
            
            if not new_heaps:
                self.status_var.set("ERROR: Invalid starting heaps.")
                return

            self.heaps = new_heaps
            self.turn_count = 0
            self.clear_log()
            self.log_move("--- GAME STARTED ---")
            self.log_move(f"INITIAL POSITION: {self.heaps}")
            self.analyze_current_state(player="Player 1 (You)")
            
        except Exception:
            self.status_var.set("ERROR: Invalid input format. Check your numbers.")

    # --- State Analysis ---
    def analyze_current_state(self, player: str):
        """Analyzes the current heap state and updates the GUI."""
        self.turn_count += 1
        
        heaps = self.heaps
        nim_sum = calculate_nim_sum(heaps)
        
        self.log_move(f"\n--- Turn {self.turn_count} ({player}'s Turn) ---")
        self.log_move(f"Current State: {heaps} | Nim-sum: {nim_sum}")
        
        # Clear old move buttons (only buttons)
        for widget in self.move_frame.winfo_children():
            # Keep the "Your Move Options" Label (row 0, col 0)
            if widget.grid_info().get('row', -1) > 0 or widget.grid_info().get('column', -1) > 0:
                 widget.destroy()

        if nim_sum == 0:
            # LOSING POSITION (P-Position)
            self.status_var.set("STATUS: LOSING POSITION (Nim-sum = 0). Opponent is winning.")
            self.status_label.config(foreground='red')
            
            self.log_move("STRATEGY: P-Position. You must make any legal move.")
            self.log_move("Please enter your chosen move into the 'Opponent Move' entry below and click 'Log Move'.")
            
            self.add_opponent_input()
            self.add_random_move_button()
            
        else:
            # WINNING POSITION (N-Position)
            self.status_var.set("STATUS: WINNING POSITION (Nim-sum ≠ 0). You can force a win.")
            self.status_label.config(foreground='green')
            
            self.move_options = self.find_optimal_moves(heaps, nim_sum)
            self.log_move("STRATEGY: N-Position. Choose an optimal move below:")

            # Add buttons for optimal moves in a COLUMN
            for idx, move in enumerate(self.move_options):
                btn_text = f"Option {idx + 1}: Remove {move['remove_amount']} from Heap {move['heap_index']} (New size: {move['new_size']})"
                action = functools.partial(self.apply_optimal_move, idx)
                
                # Place each button in a new row (column 0)
                ttk.Button(self.move_frame, text=btn_text, command=action).grid(row=idx + 1, column=0, sticky="w", pady=2, padx=10)


    # --- Rest of the class methods remain the same, but need adjustment for grid layout in move_frame ---
    
    # --- Move Calculation (No change) ---
    def find_optimal_moves(self, heaps, nim_sum):
        """Finds all optimal moves (S' = 0)."""
        optimal_moves = []
        for i, heap_size in enumerate(heaps):
            target_size = heap_size ^ nim_sum
            if target_size < heap_size:
                optimal_moves.append({
                    'heap_index': i + 1,
                    'current_size': heap_size,
                    'remove_amount': heap_size - target_size,
                    'new_size': target_size,
                    'heap_true_index': i # For internal use
                })
        return optimal_moves

    # --- Player Move Application (No change) ---
    def apply_optimal_move(self, move_index):
        """Applies the user's selected optimal move."""
        move = self.move_options[move_index]
        
        # Update the heap state
        self.heaps[move['heap_true_index']] = move['new_size']
        
        self.log_move(f"PLAYER 1 MOVED (Option {move_index + 1}): Removed {move['remove_amount']} from Heap {move['heap_index']}.")
        
        # Check for game end
        if all(h == 0 for h in self.heaps):
            self.end_game("Player 1 (You) Win!")
            return
            
        # Log the state after player's move
        self.heaps = [h for h in self.heaps if h > 0] # Remove 0 heaps
        self.log_move(f"New State: {self.heaps} (Nim-sum: {calculate_nim_sum(self.heaps)})")
        
        # Proceed to Opponent's turn
        self.analyze_current_state(player="Opponent (Computer)")

    # --- Opponent Move Simulation (Manual/Simple Random) ---
    def add_opponent_input(self):
        """Adds controls for the user to input the opponent's move."""
        # Clear existing move buttons and labels
        for widget in self.move_frame.winfo_children():
            if widget.grid_info().get('row', -1) > 0 or widget.grid_info().get('column', -1) > 0:
                 widget.destroy()

        # Place new widgets using grid
        r = 1
        ttk.Label(self.move_frame, text="Heap Index (1, 2, ...):").grid(row=r, column=0, sticky="w", padx=10)
        self.opp_heap_entry = ttk.Entry(self.move_frame, width=5)
        self.opp_heap_entry.grid(row=r, column=1, sticky="w", padx=5)
        
        r += 1
        ttk.Label(self.move_frame, text="Amount to Remove:").grid(row=r, column=0, sticky="w", padx=10)
        self.opp_remove_entry = ttk.Entry(self.move_frame, width=5)
        self.opp_remove_entry.grid(row=r, column=1, sticky="w", padx=5)
        
        r += 1
        ttk.Button(self.move_frame, text="Log Opponent Move", command=self.apply_opponent_move).grid(row=r, column=0, columnspan=2, pady=5, padx=10)
        
        self.add_random_move_button()


    def add_random_move_button(self):
        """Helper to let the user see what a random legal move is."""
        import random
        legal_moves = []
        for i, h in enumerate(self.heaps):
            for r in range(1, h + 1):
                legal_moves.append((i + 1, r))
        
        r = self.move_frame.grid_size()[1] # Get current highest row
        if legal_moves:
            random_move = random.choice(legal_moves)
            ttk.Label(self.move_frame, text=f"(e.g. Random Move: Heap {random_move[0]}, Remove {random_move[1]})", foreground='gray').grid(row=r, column=0, columnspan=2, sticky="w", padx=10)


    def apply_opponent_move(self):
        """Applies the manually entered opponent move."""
        try:
            heap_index = int(self.opp_heap_entry.get().strip())
            amount_to_remove = int(self.opp_remove_entry.get().strip())
            
            if not (1 <= heap_index <= len(self.heaps)):
                self.status_var.set("ERROR: Invalid Heap Index.")
                return
            
            heap_true_index = heap_index - 1
            current_size = self.heaps[heap_true_index]
            
            if not (1 <= amount_to_remove <= current_size):
                self.status_var.set("ERROR: Invalid remove amount. Must be 1 to " + str(current_size) + ".")
                return
            
            # Apply the move
            self.heaps[heap_true_index] -= amount_to_remove
            
            self.log_move(f"OPPONENT MOVED: Removed {amount_to_remove} from Heap {heap_index}.")

            # Check for game end
            if all(h == 0 for h in self.heaps):
                self.end_game("Opponent Wins!")
                return
            
            # Log the state after opponent's move
            self.heaps = [h for h in self.heaps if h > 0] # Remove 0 heaps
            self.log_move(f"New State: {self.heaps} (Nim-sum: {calculate_nim_sum(self.heaps)})")

            # Proceed to Player 1's turn
            self.analyze_current_state(player="Player 1 (You)")
            
        except ValueError:
            self.status_var.set("ERROR: Please enter valid numbers for index and amount.")

    def end_game(self, message):
        """Handles the end of the game."""
        self.status_var.set("GAME OVER: " + message)
        self.status_label.config(foreground='purple')
        self.log_move(f"\n--- GAME OVER: {message} ---")
        
        # Clear move frame
        for widget in self.move_frame.winfo_children():
            widget.destroy()

if __name__ == "__main__":
    root = tk.Tk()
    app = NimAdvisorApp(root)
    root.mainloop()