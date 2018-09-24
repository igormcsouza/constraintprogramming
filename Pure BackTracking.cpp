// BackTracking.cpp : Este arquivo contém a função 'main'. A execução do programa começa e termina ali.
// Igor Souza 347208
// A função bactracking recebe um Problema e um true/false para uso da função violation.

#include "pch.h"
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <stack>
#include <time.h>

using namespace std;

// Place to declare the Structs --------------------------------------------------------------------------------------

enum Relation {
	EQ, NE, LT, LE, GT, GE
};

struct Constraints {
	vector <int> coeficients; 
	int rhs; // Right Side
	Relation relation; // Type of relation
};

struct Problem {
	int numberVariables; 
	int numberConstraints;
	vector <vector <int>> domain; // each row is a vector numbered according to the domain
	// vector <int> coeficients; // Case we are talking abount min equations
	vector <Constraints> constraints; // I represent the constraints this way
};

// Auxiliaries Functions ----------------------------------------------------------------------------------------------

void printProblem(Problem P) {
	// Function to show in the screen the problem P
	cout << "------------------------------------------------------" << endl;
	cout << "Number of Variables: " << P.numberVariables << endl;
	cout << "Number of Constraints: " << P.numberConstraints << endl;
	cout << "Domain: " << endl;
	for (int rows = 0; rows < P.numberVariables; rows++) {
		cout << rows << ": ";
		for (int columns = 0; columns < P.domain[rows].size(); 
			columns++) { cout << P.domain[rows][columns] << " "; }
		cout << endl;
	}
	cout << "Constraints: " << endl;
	for (int interator = 0; interator < P.numberConstraints; interator++) {
		for (int columns = 0; columns < P.numberVariables; columns++) {
			cout << P.constraints[interator].coeficients[columns] << " ";
		}
		cout << " | " << P.constraints[interator].relation << " | " << P.constraints[interator].rhs << endl;
	}
	cout << "------------------------------------------------------" << endl;
}

Problem fixIt(Problem &P, int variableIndex, int elementToFix) {
	Problem cpy = P;

	cpy.domain[variableIndex].clear(); // Clear the whole vector
	cpy.domain[variableIndex].push_back(elementToFix); // push the element to be fixed

	return cpy;
}

int variablesAreAllFixed(Problem &top) {
	// take the Problem and return the first element which has more than 1 as domain.size()
	for (int elements = 0; elements < top.domain.size(); elements++) {
		if (top.domain[elements].size() > 1) { // if GT 1
			return elements; 
		}
	}
	return -1;
}

bool satisfiable(int lhs, Relation rel, int rhs) {
	// return the result according to the dictionary below
	if (rel == EQ) { return lhs == rhs; }
	if (rel == NE) { return lhs != rhs; }
	if (rel == LT) { return lhs < rhs; }
	if (rel == LE) { return lhs <= rhs; }
	if (rel == GT) { return lhs > rhs; }
	if (rel == GE) { return lhs >= rhs; }
}

void printOnFile(vector <Problem> &vector) {
	ofstream file;
	file.open("solucao.txt");

	cout << endl;
	for (int i = 0; i < vector.size(); i++) {
		cout << "Solution " << i << ": ";
		for (int j = 0; j < vector[i].numberVariables; j++) {
			cout << vector[i].domain[j][0] << " "; // print on the screen
			file << vector[i].domain[j][0] << " "; // print on file
		}
		cout << endl;
		file << endl;
	}

	if (vector.empty()) { cout << "Inviable" << endl; file << "Inviable";  }
}

// Main Functions are going to be placed here -----------------------------------------------------------------------

Problem read_files() {
	ifstream file;
	Problem P;

	file.open("problema.txt");

	file >> P.numberVariables; // Variables of the Problem
	file >> P.numberConstraints; // The number of constraints of the Problem

	// Reading the domain in 2 steps, first the MIN and the MAX then put in the Problem
	vector <vector <int>> auxDomain; // To help get the domain
	for (int rows = 0; rows < 2; rows++) {
		int aux;
		vector <int> vector;
		for (int columns = 0; columns < P.numberVariables; columns++) {
			file >> aux;
			vector.push_back(aux);
		}
		auxDomain.push_back(vector);
	}

	for (int rows = 0; rows < P.numberVariables; rows++) {
		int aux = auxDomain[1][rows] - auxDomain[0][rows]; // size of the domain
		int aux2 = auxDomain[0][rows]; // first element is the lower bound
		vector <int> vector;
		for (int columns = 0; columns <= aux; columns++) {
			vector.push_back(aux2 + columns); // push all the elements the domain could hold
		}
		P.domain.push_back(vector);
	}

	// Reading the RHS of the Constraints
	for (int interator = 0; interator < P.numberConstraints; interator++) {
		Constraints caux;
		file >> caux.rhs;
		P.constraints.push_back(caux);
	}

	// Reading the type of relation (remember we are using ENUM type)
	for (int interator = 0; interator < P.numberConstraints; interator++) {
		string aux;
		file >> aux;
		if (aux == "LE") P.constraints[interator].relation = EQ;
		if (aux == "NE") P.constraints[interator].relation = NE;
		if (aux == "LT") P.constraints[interator].relation = LT;
		if (aux == "LE") P.constraints[interator].relation = LE;
		if (aux == "GT") P.constraints[interator].relation = GT;
		if (aux == "GE") P.constraints[interator].relation = GE;
	}

	// Reading now the coeficients of the constraints
	for (int rows = 0; rows < P.numberConstraints; rows++) {
		int aux;
		for (int columns = 0; columns < P.numberVariables; columns++) {
			file >> aux;
			P.constraints[rows].coeficients.push_back(aux);
		}
	}

	file.close();
	return P;
}

bool violation(Problem &P) {
	// What I want in this function is to indentify whether a subProblem P is violating or not
	//the initial conditions of my main problem.

	vector <int> notFixed;

	// First save the position of all the variables which domain is not fixed
	for (int index = 0; index < P.numberVariables; index++) {
		if (P.domain[index].size() > 1) { notFixed.push_back(index); }
	}

	// Then, search if all of the not fixed domains are not important to solve a cons-est constraint
	bool flag = true;
	for (int cons = 0; cons < P.numberConstraints; cons++) { // Go through all the constraints
		for (int index = 0; index < notFixed.size(); index++) {
			if (P.constraints[cons].coeficients[notFixed[index]] != 0) flag = false;
			// If the coeficient is 0, means the contraint doesn't need the variable to have the answer;
		}
		if (flag) { // If all the unfixed variables are useless to the constraint, test if it can violate the answer...
			int result = 0;
			for (int coef = 0; coef < P.numberVariables; coef++) {
				result += P.constraints[cons].coeficients[coef] * P.domain[coef][0]; // calculate the LHS
			}
			if (!satisfiable(result, P.constraints[cons].relation, P.constraints[cons].rhs)) { return true; }
			// return true if the setting variables are violating any constraint
		}
	}
 
	// Return false if after all the searching, none constraint were violate;
	return false;
}

bool isViable(Problem &P) {
	// search the viablility of the subProblem P
	for (int cons = 0; cons < P.numberConstraints; cons++) {
		int result = 0;
		for (int coef = 0; coef < P.numberVariables; coef++) {
			result += P.constraints[cons].coeficients[coef] * P.domain[coef][0];
		}
		//This function search to know if the LHS violate the RHS according to the given Relation Type
		if (!satisfiable(result, P.constraints[cons].relation, P.constraints[cons].rhs)) { return false; }
	}

	return true;
}

vector <Problem> backtracking(Problem &P, bool useViolation) {
	// The logic of this algoritm is to find a complete set of variables belonging to its domain which are not
	// broken any constraint given. It also has a tool to find if the part-complete set of variables is already
	// violating a constraint. It does this by looking the part-fixed Problem P which all the fixed variables are
	// enough to test the constraint.

	stack <Problem> myStack;
	Problem copy;
	vector <Problem> result;

	// Start the Stack fixing the first node as X0 and all the elements in the domain of X0;
	for (int elements = P.domain[0].size() - 1; elements >= 0; elements--) {
		myStack.push(fixIt(P, 0, P.domain[0][elements]));
	}
	copy = myStack.top();
	myStack.pop();

	int count = myStack.size(); // Start the count, in the size of the actual stack
	int min = INT_MAX; // Min start with a infinity bigger enough to helps find how many interactions to
	// find the first complete

	while (myStack.size() != 0) {
		int firstNotFixed = variablesAreAllFixed(copy); // gets the first variable which domain is not fixed yet
		// If all the domains are fixed, lets push into the solution the fixed variables
		if (firstNotFixed == -1 && (useViolation || isViable(copy))){ // if it is true, or better, 
			// if suproblem P is viable, print in the result
			result.push_back(copy); 
			// The first case print in the sceen the number of interations to get a complete
			if (min > count) { cout << endl << "Interactions to get a Complete Viable Solution: " 
				<< count << endl; min = count; }
		}
		else {
			// if it's not complete, push into the vector the elements in the firstNotFixed's domain
			for (int interetor = copy.domain[firstNotFixed].size() - 1; interetor >= 0; interetor--) {
				myStack.push(fixIt(copy, firstNotFixed, copy.domain[firstNotFixed][interetor]));
				// Push back with the elements fixed
			}
		}
		while (useViolation && violation(myStack.top())) { myStack.pop(); } 
		// Try to solve before had the question, isViable?
		copy = myStack.top(); count += 1;
		myStack.pop();
		cout << "\r" << count << " "; // Show in the screen the steps it is taking
	}
	
	cout << endl << "Numero de interacoes: " << count << endl;

	return result;
}

int main()
{
	// Declare the Problem
	Problem myActivity;

	// Read Files
	myActivity = read_files();
	cout << "Read file complete..." << endl;
	printProblem(myActivity);
	
	// Go BackTracking
	double start = clock(); // Save the time it takes to do the job
	cout << "Starting the backtracking..." << endl;
	// backtracking(Problem from struct Problem and a bool to say if we should or not use violation function.
	vector <Problem> problemViability = backtracking(myActivity, true);
	double end = clock();

	// Print in a File... not yet
	cout << "Results below..." << endl;
	printOnFile(problemViability);

	cout << "Time gone: " << (end - start) / 1000 << "s!" << endl;

	return 0;
}
