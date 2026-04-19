# CFG Analyzer

Interactive web app to analyze Context-Free Grammars (CFGs) with:

- Grammar parsing and validation
- CNF (Chomsky Normal Form) conversion (step-by-step)
- CYK parsing table construction
- Parse tree reconstruction
- Leftmost derivation view
- Ambiguity detection (attempts to find two distinct parse trees)

## Tech Stack

- HTML (`index.html`)
- CSS (`CFG_Analyser_Final.css`)
- Vanilla JavaScript (`CFG_Analyser_Final.js`)

No build step or external runtime is required.

## Run Locally

1. Clone the repository:

```bash
git clone https://github.com/Rithvik911/Toc_project.git
cd Toc_project
```

2. Open `index.html` in your browser.

For best experience, use a local static server (optional):

```bash
# Python 3
python -m http.server 5500
```

Then open `http://localhost:5500`.

## How to Use

1. Enter grammar rules in the **Grammar (CFG)** box.
2. Enter the test string in **Test String** (`e` for epsilon / empty string).
3. Choose analysis speed.
4. Click **Analyze**.
5. Follow section outputs:
   - Grammar Analysis
   - CNF Conversion
   - CYK Parser
   - Parse Tree
   - Ambiguity Detection

## Grammar Input Format

- One production per line
- Use `->` between LHS and RHS
- Use `|` for alternatives
- Uppercase symbols are treated as non-terminals
- Lowercase symbols are treated as terminals
- Use `e` or `ε` for epsilon

Example:

```text
S -> AB | BC
A -> BA | a
B -> CC | b
C -> AB | a
```

## Notes

- The converter introduces helper non-terminals during CNF conversion.
- Parse tree rendering is SVG-based.
- Ambiguity detection is based on finding multiple valid parse trees for the given input string.

## Repository Structure

```text
.
├── index.html
├── CFG_Analyser_Final.css
└── CFG_Analyser_Final.js
```

## License

No license file is currently defined in this repository.
