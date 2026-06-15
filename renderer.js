
/**
 * This file is loaded via the <script> tag in the index.html file and will
 * be executed in the renderer process for that window. No Node.js APIs are
 * available in this process because `nodeIntegration` is turned off and
 * `contextIsolation` is turned on. Use the contextBridge API in `preload.js`
 * to expose Node.js functionality from the main process.
 */









class proposition {
  constructor(string) {
    this.scopeId = 0;
    this.active = true;
    this.openScopes = null;
    this.nextProp1 = null;
    this.connector = null;
    this.nextProp2 = null;
    this.value = null;
    this.derivedFromLines = [];
    this.derivedFromRule = null;
    this.assumed = false;

    if (typeof string !== "undefined") {
      string = string.replace(/\s+/g, "");

      // validate parentheses balance
      let balance = 0;
      for (let ch of string) {
        if (ch === "(") balance++;
        else if (ch === ")") balance--;
        if (balance < 0) throw new Error("Invalid: mismatched parentheses");
      }
      if (balance !== 0) throw new Error("Invalid: unbalanced parentheses");

      // recursive parse
      const parse = (expr) => {
        // strip outer parentheses
        if (expr[0] === "(" && expr[expr.length - 1] === ")") {
          let inner = expr.slice(1, -1);
          if (this.isBalanced(inner)) expr = inner;
        }

        // find main connector at top level
        let depth = 0;
        for (let i = 0; i < expr.length; i++) {
          let ch = expr[i];
          if (ch === "(") depth++;
          else if (ch === ")") depth--;
          else if (depth === 0 && ["&", "^", "=", ">"].includes(ch)) {
            // split into left/right
            let left = expr.slice(0, i);
            let right = expr.slice(i + 1);
            let node = new proposition();
            node.nextProp1 = new proposition(left);
            node.connector = ch;
            node.nextProp2 = new proposition(right);
            return node;
          }
        }

        // no connector → atomic value
        let atom = new proposition();
        atom.value = expr;
        return atom;
      };

      // helper to check balance
      this.isBalanced = (s) => {
        let b = 0;
        for (let c of s) {
          if (c === "(") b++;
          else if (c === ")") b--;
          if (b < 0) return false;
        }
        return b === 0;
      };

      // assign parsed structure to this
      let parsed = parse(string);
      Object.assign(this, parsed);
    }
  }

  returnProposition() {
    if (this.value !== null) return this.value;
    let left = this.nextProp1.returnProposition();
    let right = this.nextProp2.returnProposition();
    if (this.nextProp1.connector !== null) left = "(" + left + ")";
    if (this.nextProp2.connector !== null) right = "(" + right + ")";
    return `${left} ${this.connector} ${right}`;
  }
}

class argument
{
	constructor(input)
	{
		this.proof = [];
        this.scopeCounter = 0;
        this.openScopes = []; // stack of open, non-discharged scopeIds
        if (typeof input !== "undefined")
        {
            input.scopeId = 0;
            input.active = true;
            this.proof.push(input);
        }
	}
	
	norm(s) { return s.replaceAll(" ", ""); }

  chooseScope(...scopeIds) {
    const activeScopes = scopeIds.filter(id =>
      id === 0 || this.openScopes.includes(id)
    );
    if (activeScopes.length === 0) return 0;
    return Math.max(...activeScopes);
  }

	addProposition(input) {
  // Ensure input is a proposition instance
  if (typeof input === "string") {
    input = new proposition(input);
  } else if (!(input instanceof proposition)) {
    throw new Error("addProposition expects a proposition or a string.");
  }


  if (input.scopeId === undefined || input.scopeId === null) {
    const last = this.proof[this.proof.length - 1];
    input.scopeId = last && typeof last.scopeId === "number" ? last.scopeId : 0;
  }

  input.active = true;
  this.proof.push(input);
}

	displayArgument()
	{
		let list = [];
		//console.log(this.proof[0].returnProposition());
		for(let i = 0; i < this.proof.length; i++)
		{

			if(this.proof[i].derivedFromRule !== null && this.proof[i].assumed === true)
			{
				list[i] = i+1 + ": " + this.proof[i].returnProposition() + "    |" + this.proof[i].derivedFromLines + " " + this.proof[i].derivedFromRule + "! ASS";
				console.log(i+1 + ": " + this.proof[i].returnProposition() + "    |" + this.proof[i].derivedFromLines + " " + this.proof[i].derivedFromRule + "! ASS");
			}
			else if(this.proof[i].derivedFromRule !== null) //the derivedFromRule will only be represented if it exists, if it doesn't exist it will be null
			{
				list[i] = i+1 + ": " + this.proof[i].returnProposition() + "    |" + this.proof[i].derivedFromLines + " " + this.proof[i].derivedFromRule;
				console.log(i+1 + ": " + this.proof[i].returnProposition() + "    |" + this.proof[i].derivedFromLines + " " + this.proof[i].derivedFromRule);
			}
			else if(this.proof[i].assumed === true) //used to show when something is assumed
			{
				list[i] = i+1 + ": " + this.proof[i].returnProposition() + "    |" + this.proof[i].derivedFromLines + "! ASS";
				console.log(i+1 + ": " + this.proof[i].returnProposition() + "    |" + this.proof[i].derivedFromLines + "! ASS");
			}
			else //default, will propably be used for starting assumptions //since derivedFromLines is a list, if a list is empty it won't be represented, so it could be removed
			{
				list[i] = i+1 + ": " + this.proof[i].returnProposition() + "    |" + this.proof[i].derivedFromLines;
				console.log(i+1 + ": " + this.proof[i].returnProposition() + "    |" + this.proof[i].derivedFromLines);
			}
		}
		return list;
	}

andElimination(propLine, elimLine) {
  // --- Reject multi-line inputs early ---
  const rawPropLine = String(propLine ?? "").trim();
  if (rawPropLine.includes(",")) {
    throw new Error("You should provide just one line number for the conjunction, not a list of numbers.");
  }
  const rawElimLine = String(elimLine ?? "").trim();
  if (rawElimLine.includes(",")) {
    throw new Error("You should provide a single target proposition, not a list of statements.");
  }

  // --- Validate propLine is a positive integer ---
  const L = Number(rawPropLine);
  if (!Number.isFinite(L)) {
    throw new Error("The line number you gave isn’t valid — it should be a number.");
  }
  if (!Number.isInteger(L)) {
    throw new Error("The line number must be a whole number (like 1, 2, 3…).");
  }
  if (L <= 0) {
    throw new Error("The line number must be positive (1 or greater).");
  }
  if (L > this.proof.length) {
    throw new Error(`Line ${L} doesn’t exist — the proof only has ${this.proof.length} lines.`);
  }

  // --- Validate elimLine ---
  if (typeof elimLine !== "string" || rawElimLine === "") {
    throw new Error("You need to provide a non-empty proposition as the target conjunct.");
  }

  // --- Ensure the line is usable (active and in open scope) ---
  if (!this.isLineUsable(L)) {
    throw new Error(`Line ${L} can’t be used right now (it’s inactive or outside the current scope).`);
  }

  const prop = this.proof[L - 1];
  if (!prop) {
    throw new Error(`There’s no proposition at line ${L}.`);
  }

  // --- Ensure the proposition is a conjunction and well-formed ---
  if (prop.connector !== "&") {
    throw new Error(`Line ${L} isn’t a conjunction (A&B). Instead, it has connector: ${prop.connector ?? "none"}.`);
  }
  if (!prop.nextProp1 || !prop.nextProp2) {
    throw new Error(`The conjunction at line ${L} is incomplete — it’s missing either the left or right part.`);
  }

  // --- Helper: strip outer parentheses and normalize for comparison ---
  const stripOuterParens = (s) => {
    if (typeof s !== "string") return s;
    let t = s.replaceAll(" ", "");
    while (t.length >= 2 && t[0] === "(" && t[t.length - 1] === ")") {
      let b = 0, balanced = true;
      for (let i = 0; i < t.length; i++) {
        if (t[i] === "(") b++;
        else if (t[i] === ")") b--;
        if (b < 0) { balanced = false; break; }
      }
      if (!balanced) break;
      t = t.slice(1, -1);
    }
    return t;
  };

  const leftRaw = prop.nextProp1.returnProposition();
  const rightRaw = prop.nextProp2.returnProposition();

  const leftNorm = this.norm(stripOuterParens(leftRaw));
  const rightNorm = this.norm(stripOuterParens(rightRaw));
  const targetNorm = this.norm(stripOuterParens(rawElimLine));

  // --- Match target to exactly one conjunct ---
  if (leftNorm === targetNorm || rightNorm === targetNorm) {
    const newProp = new proposition(rawElimLine.replaceAll(" ", ""));
    newProp.derivedFromRule = "&E";
    newProp.derivedFromLines.push(L);
    newProp.scopeId = this.chooseScope(prop.scopeId);
    newProp.active = true;
    this.addProposition(newProp);
    return this.proof.length; // return new line number
  }

  // No match — provide a helpful error message
  throw new Error(
    `The proposition "${elimLine}" doesn’t match either part of the conjunction at line ${L}. ` +
    `The left part is "${leftRaw}", and the right part is "${rightRaw}".`
  );
}
/*
	andElimination(propLine, elimLine) {
    propLine = Number(propLine);
    if (!this.isLineUsable(propLine)) {
      throw new Error("Line " + propLine + " is not usable.");
    }
    const prop = this.proof[propLine - 1];
    const left = prop.nextProp1?.returnProposition();
    const right = prop.nextProp2?.returnProposition();
    const target = elimLine;
    if (prop.connector === "&" && (left === target || right === target)) {
      const newProp = new proposition(target);
      newProp.derivedFromRule = "&E";
      newProp.derivedFromLines.push(propLine);
      newProp.scopeId = this.chooseScope(prop.scopeId);
      newProp.active = true;
      this.addProposition(newProp);
    }
  }   */

andIntroduction(propLine1, propLine2, introLine) {
  // --- Reject multi-line inputs early ---
  const rawL1 = String(propLine1 ?? "").trim();
  const rawL2 = String(propLine2 ?? "").trim();
  if (rawL1 === "" || rawL2 === "") {
    throw new Error("You need to provide two line numbers in order to use conjunction introduction.");
  }
  if (rawL1.includes(",") || rawL2.includes(",")) {
    throw new Error("Each input should be a single line number, not a list of numbers separated by commas.");
  }

  // --- Validate numeric, integer, positive, and in-range ---
  const L1 = Number(rawL1);
  const L2 = Number(rawL2);

  if (!Number.isFinite(L1)) throw new Error("The first line number isn’t valid — it should be a number.");
  if (!Number.isFinite(L2)) throw new Error("The second line number isn’t valid — it should be a number.");
  if (!Number.isInteger(L1)) throw new Error("The first line number must be a whole number.");
  if (!Number.isInteger(L2)) throw new Error("The second line number must be a whole number.");
  if (L1 <= 0) throw new Error("The first line number must be positive (1 or greater).");
  if (L2 <= 0) throw new Error("The second line number must be positive (1 or greater).");
  if (L1 > this.proof.length) throw new Error(`Line ${L1} doesn’t exist — the proof only has ${this.proof.length} lines.`);
  if (L2 > this.proof.length) throw new Error(`Line ${L2} doesn’t exist — the proof only has ${this.proof.length} lines.`);

  // --- Ensure lines are usable ---
  if (!this.isLineUsable(L1)) throw new Error(`Line ${L1} can’t be used right now (it’s inactive or outside the current scope).`);
  if (!this.isLineUsable(L2)) throw new Error(`Line ${L2} can’t be used right now (it’s inactive or outside the current scope).`);

  // --- Validate introLine ---
  if (typeof introLine !== "string" || introLine.trim() === "") {
    throw new Error("You need to provide a non-empty conjunction (like A&B) as the result.");
  }
  const rawIntro = introLine.trim();
  if (rawIntro.includes(",")) {
    throw new Error("The conjunction should be a single statement, not a list.");
  }

  // --- Helpers: strip outer parentheses and normalize ---
  const stripOuterParens = (s) => {
    if (typeof s !== "string") return s;
    let t = s.replaceAll(" ", "");
    while (t.length >= 2 && t[0] === "(" && t[t.length - 1] === ")") {
      // check balance inside
      let b = 0, balanced = true;
      for (let i = 0; i < t.length; i++) {
        if (t[i] === "(") b++;
        else if (t[i] === ")") b--;
        if (b < 0) { balanced = false; break; }
      }
      if (!balanced) break;
      t = t.slice(1, -1);
    }
    return t;
  };
  const normalize = (s) => (typeof s === "string" ? s.replaceAll(" ", "") : s);

  // --- Extract source propositions and validate ---
  const p1 = this.proof[L1 - 1];
  const p2 = this.proof[L2 - 1];
  if (!p1) throw new Error(`There’s no proposition at line ${L1}.`);
  if (!p2) throw new Error(`There’s no proposition at line ${L2}.`);

  const raw1 = p1.returnProposition();
  const raw2 = p2.returnProposition();
  if (typeof raw1 !== "string" || raw1.trim() === "") throw new Error(`The proposition at line ${L1} is empty or malformed.`);
  if (typeof raw2 !== "string" || raw2.trim() === "") throw new Error(`The proposition at line ${L2} is empty or malformed.`);

  // --- Prepare normalized, parenthesis-aware forms for comparison ---
  const core1 = normalize(stripOuterParens(raw1));
  const core2 = normalize(stripOuterParens(raw2));

  // If a source has an internal connector, keep parentheses around it when forming the conjunction
  const formatted1 = (p1.connector !== null && p1.connector !== undefined) ? `(${core1})` : core1;
  const formatted2 = (p2.connector !== null && p2.connector !== undefined) ? `(${core2})` : core2;

  const expectedA = formatted1 + "&" + formatted2;
  const expectedB = formatted2 + "&" + formatted1;
  const given = normalize(rawIntro);

  // --- Matching and creation ---
  if (given === expectedA || given === expectedB) {
    const newProp = new proposition(given);
    newProp.derivedFromRule = "&I";
    newProp.derivedFromLines.push(L1, L2);
    newProp.scopeId = this.chooseScope(p1.scopeId, p2.scopeId);
    newProp.active = true;
    this.addProposition(newProp);
    return this.proof.length; // return new line number
  }

  // Helpful error message if no match
  throw new Error(
    `The conjunction you wrote doesn’t match the two lines you selected. ` +
    `It should be either "${expectedA}" or "${expectedB}", but you wrote "${given}". ` +
    `Line ${L1} says "${raw1}", and line ${L2} says "${raw2}".`
  );
}
/*
  andIntroduction(propLine1, propLine2, introLine) {
    const L1 = Number(propLine1), L2 = Number(propLine2);
    if (!this.isLineUsable(L1) || !this.isLineUsable(L2)) {
      throw new Error("Lines not usable.");
    }
    let tempLine1, tempLine2;
    introLine = introLine.replaceAll(" ", "");
    tempLine1 = this.norm(this.proof[L1 - 1].returnProposition());
    tempLine2 = this.norm(this.proof[L2 - 1].returnProposition());
    if (this.proof[L1 - 1].connector !== null) tempLine1 = "(" + tempLine1 + ")";
    if (this.proof[L2 - 1].connector !== null) tempLine2 = "(" + tempLine2 + ")";
    if (tempLine1 + "&" + tempLine2 === introLine || tempLine2 + "&" + tempLine1 === introLine) {
      const newProp = new proposition(introLine);
      newProp.derivedFromRule = "&I";
      newProp.derivedFromLines.push(L1, L2);
      newProp.scopeId = this.chooseScope(this.proof[L1 - 1].scopeId, this.proof[L2 - 1].scopeId);
      newProp.active = true;
      this.addProposition(newProp);
      }
    }   */
conditionElim(propLine1, propLine2, elimLine) {
  // --- Reject multi-line inputs early ---
  const rawL1 = String(propLine1 ?? "").trim();
  const rawL2 = String(propLine2 ?? "").trim();
  if (rawL1 === "" || rawL2 === "") {
    throw new Error("You need to provide two line numbers in order to use conditional elimination.");
  }
  if (rawL1.includes(",") || rawL2.includes(",")) {
    throw new Error("Each input should be a single line number, not a list of numbers separated by commas.");
  }

  // --- Validate numeric, integer, positive, and in-range ---
  const L1 = Number(rawL1);
  const L2 = Number(rawL2);

  if (!Number.isFinite(L1)) throw new Error("The first line number isn’t valid — it should be a number.");
  if (!Number.isFinite(L2)) throw new Error("The second line number isn’t valid — it should be a number.");
  if (!Number.isInteger(L1)) throw new Error("The first line number must be a whole number.");
  if (!Number.isInteger(L2)) throw new Error("The second line number must be a whole number.");
  if (L1 <= 0) throw new Error("The first line number must be positive (1 or greater).");
  if (L2 <= 0) throw new Error("The second line number must be positive (1 or greater).");
  if (L1 > this.proof.length) throw new Error(`Line ${L1} doesn’t exist — the proof only has ${this.proof.length} lines.`);
  if (L2 > this.proof.length) throw new Error(`Line ${L2} doesn’t exist — the proof only has ${this.proof.length} lines.`);

  // --- Ensure lines are usable ---
  if (!this.isLineUsable(L1)) throw new Error(`Line ${L1} can’t be used right now (it’s inactive or outside the current scope).`);
  if (!this.isLineUsable(L2)) throw new Error(`Line ${L2} can’t be used right now (it’s inactive or outside the current scope).`);

  // --- Validate elimLine ---
  if (typeof elimLine !== "string" || elimLine.trim() === "") {
    throw new Error("You need to provide a non-empty proposition as the target of elimination.");
  }
  const rawElim = elimLine.trim();
  if (rawElim.includes(",")) {
    throw new Error("The target proposition should be a single statement, not a list.");
  }

  // --- Extract source propositions and validate ---
  const P1 = this.proof[L1 - 1];
  const P2 = this.proof[L2 - 1];
  if (!P1) throw new Error(`There’s no proposition at line ${L1}.`);
  if (!P2) throw new Error(`There’s no proposition at line ${L2}.`);

  const raw1 = P1.returnProposition();
  const raw2 = P2.returnProposition();
  if (typeof raw1 !== "string" || raw1.trim() === "") throw new Error(`The proposition at line ${L1} is empty or malformed.`);
  if (typeof raw2 !== "string" || raw2.trim() === "") throw new Error(`The proposition at line ${L2} is empty or malformed.`);

  // --- Try Modus Ponens ---
  const tryMP = (impl, antecedent, implLine, antLine) => {
    if (impl.connector !== ">") {
      return false; // not an implication
    }
    if (!impl.nextProp1 || !impl.nextProp2) {
      throw new Error(`The implication at line ${implLine} is incomplete — it’s missing either the antecedent or the consequent.`);
    }

    const antecedentNorm = this.norm(antecedent.returnProposition());
    const implAnteNorm = this.norm(impl.nextProp1.returnProposition());
    const implConsNorm = this.norm(impl.nextProp2.returnProposition());
    const elimNorm = this.norm(rawElim);

    if (implAnteNorm === antecedentNorm && implConsNorm === elimNorm) {
      const newProp = new proposition(elimNorm);
      newProp.derivedFromRule = ">E";
      newProp.derivedFromLines.push(implLine, antLine);
      newProp.scopeId = this.chooseScope(impl.scopeId, antecedent.scopeId);
      newProp.active = true;
      this.addProposition(newProp);
      return true;
    }
    return false;
  };

  if (tryMP(P1, P2, L1, L2)) return this.proof.length;
  if (tryMP(P2, P1, L2, L1)) return this.proof.length;

  // --- Helpful error if no match ---
  throw new Error(
    `You can’t apply conditional elimination (modus ponens) with lines ${L1} and ${L2} to get "${elimLine}". ` +
    `Line ${L1} says "${raw1}", and line ${L2} says "${raw2}". For modus ponens, one line must be an implication (A>B), the other must match its antecedent (A), and the result should be the consequent (B).`
  );
}
/*
  conditionElim(propLine1, propLine2, elimLine) {
    const L1 = Number(propLine1), L2 = Number(propLine2);
    if (!this.isLineUsable(L1) || !this.isLineUsable(L2)) {
      throw new Error("Lines not usable.");
    }
    const P1 = this.proof[L1 - 1];
    const P2 = this.proof[L2 - 1];
    const tryMP = (impl, antecedent) => {
      if (impl.connector === ">" &&
          impl.nextProp1.returnProposition() === antecedent.returnProposition() &&
          impl.nextProp2.returnProposition() === elimLine) {
        const newProp = new proposition(elimLine);
        newProp.derivedFromRule = ">E";
        newProp.derivedFromLines.push(L1, L2);
        newProp.scopeId = this.chooseScope(impl.scopeId, antecedent.scopeId);
        newProp.active = true;
        this.addProposition(newProp);
        return true;
      }
      return false;
    };
    if (tryMP(P1, P2)) return;
    if (tryMP(P2, P1)) return;
  }     */

conditionalIntro(assumptionLine, conclusionLine, introLine, ruleUsed) {
  // --- Reject multi-line inputs early ---
  const rawAssumption = String(assumptionLine ?? "").trim();
  const rawConclusion = String(conclusionLine ?? "").trim();
  if (rawAssumption === "" || rawConclusion === "") {
    throw new Error("You need to provide both the assumption line and the conclusion line.");
  }
  if (rawAssumption.includes(",") || rawConclusion.includes(",")) {
    throw new Error("Each input should be a single line number, not a list of numbers separated by commas.");
  }

  // --- Validate numeric, integer, positive, and in-range ---
  const L1 = Number(rawAssumption);
  const L2 = Number(rawConclusion);

  if (!Number.isFinite(L1)) throw new Error("The assumption line number isn’t valid — it should be a number.");
  if (!Number.isFinite(L2)) throw new Error("The conclusion line number isn’t valid — it should be a number.");
  if (!Number.isInteger(L1)) throw new Error("The assumption line number must be a whole number.");
  if (!Number.isInteger(L2)) throw new Error("The conclusion line number must be a whole number.");
  if (L1 <= 0) throw new Error("The assumption line number must be positive (1 or greater).");
  if (L2 <= 0) throw new Error("The conclusion line number must be positive (1 or greater).");
  if (L1 > this.proof.length) throw new Error(`Line ${L1} doesn’t exist — the proof only has ${this.proof.length} lines.`);
  if (L2 > this.proof.length) throw new Error(`Line ${L2} doesn’t exist — the proof only has ${this.proof.length} lines.`);

  // --- Ensure lines are usable ---
  if (!this.isLineUsable(L1)) throw new Error(`Line ${L1} can’t be used right now (it’s inactive or outside the current scope).`);
  if (!this.isLineUsable(L2)) throw new Error(`Line ${L2} can’t be used right now (it’s inactive or outside the current scope).`);

  // --- Extract source propositions and validate ---
  const A = this.proof[L1 - 1];
  const C = this.proof[L2 - 1];
  if (!A) throw new Error(`There’s no proposition at line ${L1}.`);
  if (!C) throw new Error(`There’s no proposition at line ${L2}.`);

  if (!A.assumed) {
    throw new Error(`To introduce a conditional, line ${L1} must be marked as an assumption. Right now, it isn’t.`);
  }

  const rawA = A.returnProposition();
  const rawC = C.returnProposition();
  if (typeof rawA !== "string" || rawA.trim() === "") {
    throw new Error(`The assumption at line ${L1} is empty or malformed.`);
  }
  if (typeof rawC !== "string" || rawC.trim() === "") {
    throw new Error(`The conclusion at line ${L2} is empty or malformed.`);
  }

  // --- Validate introLine ---
  if (typeof introLine !== "string" || introLine.trim() === "") {
    throw new Error("You need to provide a non-empty conditional statement (like A>B) as the result.");
  }
  const rawIntro = introLine.trim();
  if (rawIntro.includes(",")) {
    throw new Error("The conditional statement should be a single expression, not a list.");
  }

  // --- Normalize and check expected conditional ---
  const expected = this.norm(rawA) + ">" + this.norm(rawC);
  const given = this.norm(rawIntro);

  if (given !== expected) {
    throw new Error(
      `The conditional you wrote doesn’t match what’s expected. Based on your assumption and conclusion, it should be "${expected}", but you wrote "${given}". ` +
      `Assumption (line ${L1}): "${rawA}", Conclusion (line ${L2}): "${rawC}".`
    );
  }

  // --- Promote the new conditional to the parent scope ---
  const parentScope = this.getParentScope(A.scopeId);

  const newProp = new proposition(given);
  newProp.derivedFromRule = ruleUsed || ">I";
  newProp.derivedFromLines.push(L1, L2);
  newProp.scopeId = parentScope;
  newProp.active = true;
  this.addProposition(newProp);

  // --- Discharge the assumption scope after promotion ---
  this.dischargeScope(A.scopeId);

  return this.proof.length; // return new line number
}
/*
  conditionalIntro(assumptionLine, conclusionLine, introLine, ruleUsed) {
    assumptionLine = Number(assumptionLine);
    conclusionLine = Number(conclusionLine);
    const A = this.proof[assumptionLine - 1];
    const C = this.proof[conclusionLine - 1];
    if (!A.assumed) throw new Error("Conditional intro requires assumption.");
    if (!this.isLineUsable(assumptionLine) || !this.isLineUsable(conclusionLine)) {
      throw new Error("Lines not usable.");
    }
    const expected = this.norm(A.returnProposition()) + ">" + this.norm(C.returnProposition());
    if (this.norm(introLine) !== expected) {
      throw new Error("Intro line does not match expected conditional.");
    }
    
    
    // promote the new conditional to the parent scope
  const parentScope = this.getParentScope(A.scopeId);

  const newProp = new proposition(introLine);
  newProp.derivedFromRule = ruleUsed;
  newProp.derivedFromLines.push(assumptionLine, conclusionLine);
  newProp.scopeId = parentScope;
  newProp.active = true;
  this.addProposition(newProp);

  // discharge the assumption scope after promotion
  this.dischargeScope(A.scopeId);
  }   */

biconditionalElim(lineA, lineB, elimLine) {
  // --- Reject multi-line inputs early ---
  const rawL1 = String(lineA ?? "").trim();
  const rawL2 = String(lineB ?? "").trim();
  if (rawL1 === "" || rawL2 === "") {
    throw new Error("You need to provide both line numbers in order to use biconditional elimination.");
  }
  if (rawL1.includes(",") || rawL2.includes(",")) {
    throw new Error("Each input should be a single line number, not a list of numbers separated by commas.");
  }

  // --- Validate numeric, integer, positive, and in-range ---
  const L1 = Number(rawL1);
  const L2 = Number(rawL2);

  if (!Number.isFinite(L1)) throw new Error("The first line number isn’t valid — it should be a number.");
  if (!Number.isFinite(L2)) throw new Error("The second line number isn’t valid — it should be a number.");
  if (!Number.isInteger(L1)) throw new Error("The first line number must be a whole number.");
  if (!Number.isInteger(L2)) throw new Error("The second line number must be a whole number.");
  if (L1 <= 0) throw new Error("The first line number must be positive (1 or greater).");
  if (L2 <= 0) throw new Error("The second line number must be positive (1 or greater).");
  if (L1 > this.proof.length) throw new Error(`Line ${L1} doesn’t exist — the proof only has ${this.proof.length} lines.`);
  if (L2 > this.proof.length) throw new Error(`Line ${L2} doesn’t exist — the proof only has ${this.proof.length} lines.`);

  // --- Ensure lines are usable ---
  if (!this.isLineUsable(L1)) throw new Error(`Line ${L1} can’t be used right now (it’s inactive or outside the current scope).`);
  if (!this.isLineUsable(L2)) throw new Error(`Line ${L2} can’t be used right now (it’s inactive or outside the current scope).`);

  // --- Validate elimLine ---
  if (typeof elimLine !== "string" || elimLine.trim() === "") {
    throw new Error("You need to provide a non-empty proposition as the target of elimination.");
  }
  const rawElim = elimLine.trim();
  if (rawElim.includes(",")) {
    throw new Error("The target proposition should be a single statement, not a list.");
  }

  // --- Extract source propositions and validate ---
  const P1 = this.proof[L1 - 1];
  const P2 = this.proof[L2 - 1];
  if (!P1) throw new Error(`There’s no proposition at line ${L1}.`);
  if (!P2) throw new Error(`There’s no proposition at line ${L2}.`);

  let eqProp, sideProp;
  if (P1.connector === "=") { eqProp = P1; sideProp = P2; }
  else if (P2.connector === "=") { eqProp = P2; sideProp = P1; }
  else {
    throw new Error(`To use biconditional elimination, one of the lines must be a biconditional (P=Q). Neither line ${L1} nor ${L2} is.`);
  }

  if (!eqProp.nextProp1 || !eqProp.nextProp2) {
    throw new Error(`The biconditional at line ${eqProp === P1 ? L1 : L2} is incomplete — it’s missing either the left or right side.`);
  }

  const leftRaw = eqProp.nextProp1.returnProposition();
  const rightRaw = eqProp.nextProp2.returnProposition();
  const sideRaw = sideProp.returnProposition();

  if (typeof leftRaw !== "string" || leftRaw.trim() === "") {
    throw new Error(`The left side of the biconditional at line ${eqProp === P1 ? L1 : L2} is empty or malformed.`);
  }
  if (typeof rightRaw !== "string" || rightRaw.trim() === "") {
    throw new Error(`The right side of the biconditional at line ${eqProp === P1 ? L1 : L2} is empty or malformed.`);
  }
  if (typeof sideRaw !== "string" || sideRaw.trim() === "") {
    throw new Error(`The proposition at line ${eqProp === P1 ? L2 : L1} is empty or malformed.`);
  }

  // --- Normalize and check side match ---
  const leftNorm = this.norm(leftRaw);
  const rightNorm = this.norm(rightRaw);
  const sideNorm = this.norm(sideRaw);
  const elimNorm = this.norm(rawElim);

  let inferred = null;
  if (sideNorm === leftNorm) inferred = rightRaw;
  else if (sideNorm === rightNorm) inferred = leftRaw;
  else {
    throw new Error(
      `The side proposition "${sideRaw}" doesn’t match either part of the biconditional. It should match either "${leftRaw}" or "${rightRaw}".`
    );
  }

  // --- Check elimLine matches inferred ---
  if (elimNorm !== this.norm(inferred)) {
    throw new Error(
      `The proposition you’re trying to eliminate doesn’t match the correct inference. From "${sideRaw}" and "${leftRaw}=${rightRaw}", the result should be "${inferred}", but you wrote "${elimLine}".`
    );
  }

  // --- Create new proposition ---
  const newProp = new proposition(elimNorm);
  newProp.derivedFromRule = "=E";
  newProp.derivedFromLines.push(L1, L2);
  newProp.scopeId = this.chooseScope(eqProp.scopeId, sideProp.scopeId);
  newProp.active = true;
  this.addProposition(newProp);

  return this.proof.length; // return new line number
}
/*
  biconditionalElim(lineA, lineB, elimLine) {
    const L1 = Number(lineA), L2 = Number(lineB);
    if (!this.isLineUsable(L1) || !this.isLineUsable(L2)) {
      throw new Error("Lines not usable.");
    }
    const P1 = this.proof[L1 - 1];
    const P2 = this.proof[L2 - 1];
    let eqProp, sideProp;
    if (P1.connector === "=") { eqProp = P1; sideProp = P2; }
    else if (P2.connector === "=") { eqProp = P2; sideProp = P1; }
    else throw new Error("Neither line is biconditional.");
    const left = eqProp.nextProp1.returnProposition();
    const right = eqProp.nextProp2.returnProposition();
    const side = sideProp.returnProposition();
    let inferred = null;
    if (this.norm(side) === this.norm(left)) inferred = right;
    else if (this.norm(side) === this.norm(right)) inferred = left;
    else throw new Error("Side does not match biconditional.");
    if (this.norm(inferred) !== this.norm(elimLine)) {
      throw new Error("Elim line does not match expected.");
    }
    const newProp = new proposition(elimLine);
    newProp.derivedFromRule = "=E";
    newProp.derivedFromLines.push(L1, L2);
    newProp.scopeId = this.chooseScope(eqProp.scopeId, sideProp.scopeId);
    newProp.active = true;
    this.addProposition(newProp);
  }   */


biconditionalIntro(linePQ, lineQP, derivedStatement, ruleUsed) {
  const rawPQ = String(linePQ ?? "").trim();
  const rawQP = String(lineQP ?? "").trim();
  if (rawPQ === "" || rawQP === "") {
    throw new Error("You need to provide both line numbers for the implications.");
  }
  if (rawPQ.includes(",") || rawQP.includes(",")) {
    throw new Error("Each input should be a single line number, not a list of numbers.");
  }

  const L1 = Number(rawPQ);
  const L2 = Number(rawQP);

  if (!Number.isFinite(L1)) throw new Error("The first line number isn’t valid — it should be a number.");
  if (!Number.isFinite(L2)) throw new Error("The second line number isn’t valid — it should be a number.");
  if (!Number.isInteger(L1)) throw new Error("The first line number must be a whole number.");
  if (!Number.isInteger(L2)) throw new Error("The second line number must be a whole number.");
  if (L1 <= 0) throw new Error("The first line number must be positive (1 or greater).");
  if (L2 <= 0) throw new Error("The second line number must be positive (1 or greater).");
  if (L1 > this.proof.length) throw new Error(`Line ${L1} doesn’t exist — the proof only has ${this.proof.length} lines.`);
  if (L2 > this.proof.length) throw new Error(`Line ${L2} doesn’t exist — the proof only has ${this.proof.length} lines.`);

  if (!this.isLineUsable(L1)) throw new Error(`Line ${L1} can’t be used right now (it’s inactive or outside the current scope).`);
  if (!this.isLineUsable(L2)) throw new Error(`Line ${L2} can’t be used right now (it’s inactive or outside the current scope).`);

  const fPQ = this.proof[L1 - 1];
  const fQP = this.proof[L2 - 1];
  if (!fPQ) throw new Error(`There’s no proposition at line ${L1}.`);
  if (!fQP) throw new Error(`There’s no proposition at line ${L2}.`);

  if (fPQ.connector !== ">" || fQP.connector !== ">") {
    throw new Error(`Both lines need to be implications. Line ${L1} has connector "${fPQ.connector ?? "none"}", and line ${L2} has connector "${fQP.connector ?? "none"}".`);
  }

  if (!fPQ.nextProp1 || !fPQ.nextProp2) {
    throw new Error(`The implication at line ${L1} is incomplete — it’s missing either the antecedent or the consequent.`);
  }
  if (!fQP.nextProp1 || !fQP.nextProp2) {
    throw new Error(`The implication at line ${L2} is incomplete — it’s missing either the antecedent or the consequent.`);
  }

  const P = fPQ.nextProp1.returnProposition();
  const Q = fPQ.nextProp2.returnProposition();
  const Q2 = fQP.nextProp1.returnProposition();
  const P2 = fQP.nextProp2.returnProposition();

  if (this.norm(P) !== this.norm(P2) || this.norm(Q) !== this.norm(Q2)) {
    throw new Error(`The second implication should be the reverse of the first. Right now line ${L1} says "${P} > ${Q}", but line ${L2} says "${Q2} > ${P2}".`);
  }

  if (typeof derivedStatement !== "string" || derivedStatement.trim() === "") {
    throw new Error("You need to provide a biconditional statement (like P=Q) as the derived result.");
  }
  const rawDerived = derivedStatement.trim();
  if (rawDerived.includes(",")) {
    throw new Error("The derived statement should be a single biconditional, not a list.");
  }

  const expected = this.norm(P) + "=" + this.norm(Q);
  const given = this.norm(rawDerived);
  if (given !== expected) {
    throw new Error(`The biconditional you wrote doesn’t match what’s expected. It should be "${expected}", but you wrote "${given}".`);
  }

  const newProp = new proposition(given);
  newProp.derivedFromRule = ruleUsed || "=I";
  newProp.derivedFromLines.push(L1, L2);
  newProp.scopeId = this.chooseScope(fPQ.scopeId, fQP.scopeId);
  newProp.active = true;
  this.addProposition(newProp);

  return this.proof.length;
}
/*
  biconditionalIntro(linePQ, lineQP, derivedStatement, ruleUsed) {
    const fPQ = this.proof[linePQ - 1];
    const fQP = this.proof[lineQP - 1];
    if (!this.isLineUsable(linePQ) || !this.isLineUsable(lineQP)) {
      throw new Error("Lines not usable.");
    }
    if (fPQ.connector !== ">" || fQP.connector !== ">") {
      throw new Error("Need two implications.");
    }
    const P = fPQ.nextProp1.returnProposition();
    const Q = fPQ.nextProp2.returnProposition();
    const Q2 = fQP.nextProp1.returnProposition();
    const P2 = fQP.nextProp2.returnProposition();
    if (this.norm(P) !== this.norm(P2) || this.norm(Q) !== this.norm(Q2)) {
      throw new Error("Second implication must be reverse.");
    }
    const newProp = new proposition(derivedStatement);
    newProp.derivedFromRule = ruleUsed;
    newProp.derivedFromLines.push(linePQ, lineQP);
    newProp.scopeId = this.chooseScope(fPQ.scopeId, fQP.scopeId);
    newProp.active = true;
    this.addProposition(newProp);
  }   */

  orIntroduction(lineNum, introLine) {
    lineNum = Number(lineNum);
    if (!this.isLineUsable(lineNum)) {
      throw new Error("Line not usable.");
    }
    const baseProp = this.proof[lineNum - 1];
    const normalizedIntro = this.norm(introLine);

    // Check if introLine is baseProp ∨ something OR something ∨ baseProp
    const leftCandidate = this.norm(baseProp.returnProposition()) + "^" + this.norm(introLine.replace(this.norm(baseProp.returnProposition()), ""));
    const rightCandidate = this.norm(introLine);

    if (
      normalizedIntro.startsWith(this.norm(baseProp.returnProposition()) + "^") ||
      normalizedIntro.endsWith("^" + this.norm(baseProp.returnProposition()))
    ) {
      const newProp = new proposition(introLine);
      newProp.derivedFromRule = "^I"; // Or Introduction
      newProp.derivedFromLines.push(lineNum);
      newProp.scopeId = this.chooseScope(baseProp.scopeId);
      newProp.active = true;
      this.addProposition(newProp);
    } else {
      throw new Error("Intro line does not match expected disjunction.");
    }
  }

  orElimination(orLine, assumptionLine1, conclusionLine1, assumptionLine2, conclusionLine2, elimLine) {
    orLine = Number(orLine);
    assumptionLine1 = Number(assumptionLine1);
    conclusionLine1 = Number(conclusionLine1);
    assumptionLine2 = Number(assumptionLine2);
    conclusionLine2 = Number(conclusionLine2);

    if (!this.isLineUsable(orLine)) throw new Error("Or line not usable.");
    const disj = this.proof[orLine - 1];
    if (disj.connector !== "^") throw new Error("Line is not a disjunction.");

    const left = disj.nextProp1.returnProposition();
    const right = disj.nextProp2.returnProposition();
    const concl1 = this.proof[conclusionLine1 - 1].returnProposition();
    const concl2 = this.proof[conclusionLine2 - 1].returnProposition();

    if (this.norm(concl1) !== this.norm(elimLine) || this.norm(concl2) !== this.norm(elimLine)) {
      throw new Error("Conclusions do not match elim line.");
    }

    // Build new proposition R
    const newProp = new proposition(elimLine);
    newProp.derivedFromRule = "^E"; // Or Elimination
    newProp.derivedFromLines.push(orLine, assumptionLine1, conclusionLine1, assumptionLine2, conclusionLine2);
    newProp.scopeId = this.chooseScope(disj.scopeId);
    newProp.active = true;
    this.addProposition(newProp);
  }

  negationIntro(startLine, stopLine, derivedLine, ruleUsed) {
  startLine = Number(startLine);
  stopLine = Number(stopLine);

  const A = this.proof[startLine - 1];

  if (!A.assumed) {
    throw new Error("Negation introduction requires an assumption at the start line.");
  }
  if (!this.isLineUsable(startLine) || !this.isLineUsable(stopLine)) {
    throw new Error("Start or stop line not usable.");
  }

  // Expected form: -(assumption proposition)
  const expected = "-" + this.norm(A.returnProposition());
  if (this.norm(derivedLine) !== expected) {
    throw new Error("Derived line does not match expected negation.");
  }

  // Require explicit rule specification
  if (ruleUsed !== "-I") {
    throw new Error("Rule must be specified as -I for negation introduction.");
  }

  // --- NEW: Search for contradiction pair between startLine and stopLine ---
  let foundContradiction = false;
  let contradictionLines = [];

  for (let i = startLine; i <= stopLine; i++) {
    const p1 = this.proof[i - 1];
    if (!this.isLineUsable(i)) continue;

    for (let j = i + 1; j <= stopLine; j++) {
      const p2 = this.proof[j - 1];
      if (!this.isLineUsable(j)) continue;

      const expr1 = this.norm(p1.returnProposition());
      const expr2 = this.norm(p2.returnProposition());

      if (expr1 === "-" + expr2 || expr2 === "-" + expr1) {
        foundContradiction = true;
        contradictionLines = [i, j];
        break;
      }
    }
    if (foundContradiction) break;
  }

  if (!foundContradiction) {
    throw new Error("No contradiction (P and -P) found between the specified lines.");
  }

  // Promote -P to parent scope
  const parentScope = this.getParentScope(A.scopeId);

  const newProp = new proposition(derivedLine);
  newProp.derivedFromRule = ruleUsed;
  newProp.derivedFromLines.push(startLine, ...contradictionLines, stopLine);
  newProp.scopeId = parentScope;
  newProp.active = true;
  this.addProposition(newProp);

  // Discharge the assumption scope
  this.dischargeScope(A.scopeId);
}

reiterate(lineNum, derivedLine, ruleUsed) {
  lineNum = Number(lineNum);

  if (!this.isLineUsable(lineNum)) {
    throw new Error("Line not usable.");
  }

  const prop = this.proof[lineNum - 1];
  const original = this.norm(prop.returnProposition());

  // Check that the derived line matches the original proposition
  if (this.norm(derivedLine) !== original) {
    throw new Error("Derived line must match the reiterated proposition.");
  }

  // Require explicit rule specification
  if (ruleUsed !== "R") {
    throw new Error("Rule must be specified as R for reiteration.");
  }

  // Build new proposition
  const newProp = new proposition(derivedLine);
  newProp.derivedFromRule = ruleUsed;
  newProp.derivedFromLines.push(lineNum);
  newProp.scopeId = this.chooseScope(prop.scopeId);
  newProp.active = true;
  this.addProposition(newProp);
}

  assume(assumedProp) {
    const assProp = new proposition(assumedProp);
    assProp.assumed = true;
    this.scopeCounter += 1;
    const newScope = this.scopeCounter;
    assProp.scopeId = newScope;
    assProp.active = true;
    this.openScopes.push(newScope);
    this.addProposition(assProp);
    return this.proof.length;
  }
	
	// Discharge a scope: deactivate all its lines and remove from openScopes
  dischargeScope(scopeId) {
    // Enforce proper nesting: only discharge the most recent scope
    if (this.openScopes.length === 0) {
        throw new Error("No open scopes to discharge.");
    }
    const currentScope = this.openScopes[this.openScopes.length - 1];
    if (currentScope !== scopeId) {
        throw new Error(`Scopes must be discharged in order (expected ${currentScope}, got ${scopeId}).`);
    }

    // Pop the scope
    this.openScopes.pop();

    // Deactivate all propositions in this scope
    for (const p of this.proof) {
        if (p.scopeId === scopeId) {
            p.active = false;
        }
    }
}
    
    isLineUsable(lineNum)
    {
        const p = this.proof[lineNum - 1];
        if (!p) return false;
        if (p.active === false) return false;
        if (p.scopeId === 0) return true;            // global
        return this.openScopes.includes(p.scopeId);  // scope must be open
    }
    
    getParentScope(scopeId) {
  const idx = this.openScopes.lastIndexOf(scopeId);
  if (idx === -1) {
    // scope already discharged or not found → default to global
    return 0;
  }
  return idx > 0 ? this.openScopes[idx - 1] : 0;
}
}




let goal = new argument();

// --- Error UI helpers ---
function showError(err) {
  const el = document.getElementById('errorMessage');
  if (!el) return;
  const message = (err && err.message) ? err.message : String(err);
  el.textContent = "Error: " + message;
  el.style.display = "block";
}

function clearError() {
  const el = document.getElementById('errorMessage');
  if (!el) return;
  el.textContent = "";
  el.style.display = "none";
}


// --- Updated displayArgument that clears errors on success ---
function displayArgument() {
  clearError();

  let list = document.getElementById('displayArgument');
  list.innerHTML = "";

  let scopeStack = [];

  goal.proof.forEach((prop, i) => {
    let line = document.createElement('div');
    line.classList.add("proof-line");
    line.textContent = `${i+1}: ${prop.returnProposition()} | ${prop.derivedFromLines.join(",")} ${prop.derivedFromRule || ""}${prop.assumed ? " [ASSUMED]" : ""}`;

    // If assumption, start a new scope container
    if (prop.assumed) {
      let scopeDiv = document.createElement('div');
      scopeDiv.classList.add("scope");
      scopeDiv.appendChild(line);
      list.appendChild(scopeDiv);
      scopeStack.push({id: prop.scopeId, div: scopeDiv});
    } else {
      // find the innermost open scope
      let currentScope = scopeStack[scopeStack.length - 1];
      if (currentScope) {
        currentScope.div.appendChild(line);
      } else {
        list.appendChild(line);
      }
    }

    // If scope is discharged, close it
    if (!prop.active && prop.assumed) {
      scopeStack.pop();
    }
  });
}
/*
function displayArgument() {
  let list = document.getElementById('displayArgument');
  list.innerHTML = "";

  let scopeStack = [];

  goal.proof.forEach((prop, i) => {
    let line = document.createElement('div');
    line.classList.add("proof-line");
    line.textContent = `${i+1}: ${prop.returnProposition()} | ${prop.derivedFromLines.join(",")} ${prop.derivedFromRule || ""}${prop.assumed ? " [ASSUMED]" : ""}`;

    // If assumption, start a new scope container
    if (prop.assumed) {
      let scopeDiv = document.createElement('div');
      scopeDiv.classList.add("scope");
      scopeDiv.appendChild(line);
      list.appendChild(scopeDiv);
      scopeStack.push({id: prop.scopeId, div: scopeDiv});
    } else {
      // find the innermost open scope
      let currentScope = scopeStack[scopeStack.length - 1];
      if (currentScope) {
        currentScope.div.appendChild(line);
      } else {
        list.appendChild(line);
      }
    }

    // If scope is discharged, close it
    if (!prop.active && prop.assumed) {
      scopeStack.pop();
    }
  });
}         */



function makeAssumption() {
  try {
    let assumptionText = document.getElementById('assumption').value;
    if (assumptionText.trim() === "") return;
    goal.assume(assumptionText);
    displayArgument();
  } catch (err) {
    showError(err);
  }
}
/*
function makeAssumption() {
  let assumptionText = document.getElementById('assumption').value;
  if (assumptionText.trim() === "") return;

  goal.assume(assumptionText);
  displayArgument();
}   */


function makeProposition(){
  try {
    let a = new proposition(document.getElementById('prop1').value);
    goal.addProposition(a);
    displayArgument();
  } catch (err) {
    showError(err);
  }
}
/*
function makeProposition(){
  let a = new proposition(document.getElementById('prop1').value);
  goal.addProposition(a);

    displayArgument();
}   */

function deriveProposition(){
  try {
    let newLine = document.getElementById('newLine').value;
    let fromLines = document.getElementById('fromLines').value;
    let fromRule = document.getElementById('fromRule').value;
 
    if(fromRule === "&E") {
        goal.andElimination(fromLines, newLine);
    }
    else if(fromRule === "&I") {
        let [firstNum, secondNum] = fromLines.replaceAll(" ", "").split(",");
        goal.andIntroduction(firstNum, secondNum, newLine);
    }
    else if(fromRule === ">E") {
        let [firstNum, secondNum] = fromLines.replaceAll(" ", "").split(",");
        goal.conditionElim(firstNum, secondNum, newLine);
    }
    else if(fromRule === ">I") {
        let [assumptionLine, conclusionLine] = fromLines.replaceAll(" ", "").split(",");
        goal.conditionalIntro(assumptionLine, conclusionLine, newLine, ">I");
    }
    else if(fromRule === "=I") {
        let [linePQ, lineQP] = fromLines.replaceAll(" ", "").split(",");
        goal.biconditionalIntro(linePQ, lineQP, newLine, "=I");
    }
    else if(fromRule === "=E") {
        let [lineA, lineB] = fromLines.replaceAll(" ", "").split(",");
        goal.biconditionalElim(lineA, lineB, newLine);
    }
    else if(fromRule === "^I") {
        let [lineNum] = fromLines.replaceAll(" ", "").split(",");
        goal.orIntroduction(lineNum, newLine);
    }
    else if(fromRule === "^E") {
        let [orLine, assumptionLine1, conclusionLine1, assumptionLine2, conclusionLine2] =
        fromLines.replaceAll(" ", "").split(",");
        goal.orElimination(orLine, assumptionLine1, conclusionLine1, assumptionLine2, conclusionLine2, newLine);
    }
    else if(fromRule === "-I") {
        let [startLine, stopLine] = fromLines.replaceAll(" ", "").split(",");
        goal.negationIntro(startLine, stopLine, newLine, fromRule);
    }
    else if(fromRule === "R") {
        let [lineNum] = fromLines.replaceAll(" ", "").split(",");
        goal.reiterate(lineNum, newLine, fromRule);
    }
    else {
      // If rule is empty or unknown, throw to inform user
      if (!fromRule || fromRule.trim() === "") {
        throw new Error("No rule specified.");
      } else {
        throw new Error("Unknown rule: " + fromRule);
      }
    }

  displayArgument();
  }
  catch (err)
  {
    showError(err);
  }

    //displayArgument();
}

/**
 * Cascade undo for the last line:
 * - Removes the last line and any lines that (directly or indirectly) depend on it.
 * - Reopens discharged assumption scopes when a promoted line that discharged them is removed,
 *   provided the assumption line itself is not being removed.
 * - Cleans up openScopes to remove scopes with no active propositions.
 */
function undoLastLine() {
  if (!goal || !Array.isArray(goal.proof) || goal.proof.length === 0) return;

  const lastIndex = goal.proof.length; // 1-based index of last line

  // 1) Build set of lines to remove (transitive dependents)
  const toRemove = new Set();
  const queue = [lastIndex];
  toRemove.add(lastIndex);

  while (queue.length > 0) {
    const cur = queue.shift();
    for (let i = 1; i <= goal.proof.length; i++) {
      if (toRemove.has(i)) continue;
      const p = goal.proof[i - 1];
      if (!p || !Array.isArray(p.derivedFromLines)) continue;
      for (const ref of p.derivedFromLines) {
        if (Number(ref) === cur) {
          toRemove.add(i);
          queue.push(i);
          break;
        }
      }
    }
  }

  // 2) Detect promoted lines among those being removed and reopen scopes if needed
  const promoteRules = new Set([">I", "-I", "=I", "^I"]); // add other discharge rules if you use them

  function reopenScopeIfNeeded(scopeId) {
    if (!scopeId || scopeId === 0) return;
    if (!goal.openScopes.includes(scopeId)) goal.openScopes.push(scopeId);
    for (const p of goal.proof) {
      if (p.scopeId === scopeId) p.active = true;
    }
  }

  for (const idx of Array.from(toRemove)) {
    const p = goal.proof[idx - 1];
    if (!p) continue;
    if (p.derivedFromRule && promoteRules.has(p.derivedFromRule)) {
      for (const ref of p.derivedFromLines) {
        const refNum = Number(ref);
        if (!Number.isFinite(refNum)) continue;
        const refProp = goal.proof[refNum - 1];
        if (!refProp) continue;
        // If the referenced line is an assumption and that assumption is NOT being removed,
        // reopen its scope so the user can continue working inside it.
        if (refProp.assumed && !toRemove.has(refNum)) {
          reopenScopeIfNeeded(refProp.scopeId);
        }
      }
    }
  }

  // 3) Remove the lines (keep only those not in toRemove)
  const newProof = [];
  for (let i = 1; i <= goal.proof.length; i++) {
    if (!toRemove.has(i)) newProof.push(goal.proof[i - 1]);
  }
  goal.proof = newProof;

  // 4) Cleanup openScopes: keep only scopes that still have active propositions
  goal.openScopes = goal.openScopes.filter(sid => {
    if (!sid || sid === 0) return false;
    return goal.proof.some(p => p.scopeId === sid && p.active !== false);
  });

  // 5) Re-render UI
  displayArgument();
}

// undoLastLine already exists in your file; expose a wrapper that catches errors
function undoLastLineWrapper() {
  try {
    undoLastLine(); // existing function in renderer.js
    displayArgument();
  } catch (err) {
    showError(err);
  }
}


// Expose to global scope so the HTML button can call it
window.undoLastLine = undoLastLine;
