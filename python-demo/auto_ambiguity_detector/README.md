### Dependency

---

All codes should run under python3. 

Packages used

1. PuLP: a linear programming solver
2. Scipy: a library used for scientific computing
3. Numpy: a library for mathematical computing
4. PLY: a parsing tool for semantic analysis (not used, the parser is based on regex right now.)

You may use pip3 to install those packages.

### Folders

##### Examples

---

There are some if statements examples written in Promela. They are used to test the ambiguity detector.

##### LP_demo

----

There are two demos about linear programming. LP_PuLP_demo is based on PuLP. LP_Scipy_demo is based on Scipy. Scipy only supports linear programming. But PuLP supports linear programming, integer programming, and three party linear programming solver with a better performance. Scipy is discarded.

##### Test_script
---

This folder is used to store the generated test script from the simulator.

### Checker / Files

##### ply.py

----

A parser based on PLY. It's not finished yet. Although the PLY is a more advanced parser, we don't need its feature now. I will finish it when needed.

##### Promela_parser.py

---

A parser based on regex. It is a python class for extracting needed Promela code fragments. It's not runnable, but the checkers are based on it. At present, it can extract if statements, conditions, and variables.

##### ambiguity_checker_simulator.py

----

**args:** the simulator accepts one arg - the Promela code's relative path.

```shell
$python3 ambiguity_checker_simulator.py examples/examples.pml
```

**output**: the simulator will generate some test scripts under *test_scripts* folder to test each if statements in the given Promela code.

**method:** the simulator randomly generates values between 1 to 10000 and assign them to the variables in the if statements. If there is more than 1 condition simultaneously true. A flaw / an ambiguity is found.

**pros: ** this simulator works for all cases. No matter how sophisticate the conditions are. The simulator will find a solution with massive test rounds.

**cons:** the simulator doesn't prove to find a solution. The simulator may not be able to find the edge cases.

##### ambiguity_checker_LP.py

----

**args**: the checker accepts one arg - the Promela code's relative path

```shell
$python3 ambiguity_checker_LP.py example/example2.pml
```

**output**: the check will generate a text file named *report.txt* which contains the result from the LP

**method**: the checker is based on linear programming / integer programming. The check will test all combinations of if conditions (nC2 - n choose 2). No test scripts generated. The checker detects the ambiguities by finding the minimum sum of all variables. Because the variables in our research are mostly non-negative, there always exists a minimum sum if there is a solution.

**pros:** the linear programming solver is proved to find a solution if there is one. It takes a shorter time to find the answer than the simulator.

**cons: **the solver can't solve complex conditions - thrice and above. The running time increases dramatically when we have complex cases. Doesn't support > or < in the integer programming because all > and < can be replaced by <= with adding / subtracting 1.



### Reference link

[Linear Programming](https://en.wikipedia.org/wiki/Linear_programming)

[Integer Programming](https://en.wikipedia.org/wiki/Integer_programming)

[PuLP](https://coin-or.github.io/pulp/)