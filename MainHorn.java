import java.io.BufferedReader;
import java.io.FileReader;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

public class MainHorn {

	public static void main(String[] args) {
		String str, name;
		boolean negation;
		CNFClause knowledgeBase = new CNFClause();
		Vector<CNFSubClause> subClauses = new Vector<CNFSubClause>();
		Literal q = new Literal("NOT DEFINED", false);
		
		try {
			BufferedReader kb = new BufferedReader(new FileReader("C:\\tmp\\kb.txt"));
			System.out.println("Type Literal to be tested");
			BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
			
			try {
				/*
				String s = br.readLine();
				if(s.contains(" ^ ")) {
					String[] testClause = s.split(" ^ ");
					for(String sub : testClause) {
						String[] test = sub.split(" v ");
						for(String l: test) {
							String[] lit = l.split("-");
							name = lit[0];
							negation = Boolean.valueOf(lit[1]);
							testSub.getLiterals().add(new Literal(name, negation));
						}
					}
				}
				*/
				
				String s = br.readLine();
				name = s;
				q = new Literal(name, false);
				
				while ((str = kb.readLine()) != null) {
					CNFSubClause subClause = new CNFSubClause();
					String[] literals = str.split(" v ");
					for(String l: literals) {
						String[] literal = l.split("-");
						name = literal[0];
						negation = Boolean.valueOf(literal[1]);
						subClause.getLiterals().add(new Literal(name, negation));
					}
					subClauses.add(subClause);
					
				}
			}
			finally {
            	kb.close();
            	br.close();
            }
			
			knowledgeBase.theClauses = subClauses;
		}
		catch(Exception e) {
			System.out.println(e);
		}
			
		System.out.println("----------------------------------------------------");
        System.out.println();

        //Running resolution
        boolean b = PL_FC_Entails(knowledgeBase, q);
        q.print();
        System.out.println("is " + b);
	}
	
	public static boolean PL_FC_Entails(CNFClause KB, Literal q) {
		 //We create a CNFClause that contains all the clauses of our Knowledge Base, converted to Horn form
        CNFClause clauses = new CNFClause();
        ArrayList<Literal> agenda = new ArrayList<Literal>(); //A list of symbols, initially know to be true
        
        for(CNFSubClause sub : KB.getSubclauses()) {
			CNFSubClause newSub = new CNFSubClause();
			if(sub.getLiterals().size() == 1) {
				Literal lit = sub.getLiteralsList().next();
				if(!agenda.contains(lit)) {
					agenda.add(lit);	
				}
			}
        	for(Literal l : sub.getLiterals()) {
        		if(l.getNeg() == true) {
        			String newName = "N" + l.getName();
        			newSub.getLiterals().add(new Literal(newName, !l.getNeg()));
        		}
        	}
        	clauses.getSubclauses().add(newSub);
        }

        HashMap<CNFSubClause, Integer> count = new HashMap<CNFSubClause, Integer>(); // a "table" indexed by clause, initially the number of premises for that clause
        for(CNFSubClause sub : clauses.getSubclauses()) {
        	count.put(sub, sub.getLiterals().size()-1);
        }
        
        HashMap<Literal, Boolean> inferred = new HashMap<Literal, Boolean>(); //a "table" indexed by symbol, each entry initially false
        for(CNFSubClause sub : clauses.getSubclauses()) {
        	for(Literal l : sub.getLiterals()) {
        		inferred.putIfAbsent(l, false);
        	}
        }
        
        //Loop through agenda
        while(!agenda.isEmpty()) {
        	//For every literal we know to be true (because it exists in our knowledge base as a fact)
        	Literal p = agenda.remove(0);
        	//Check if it has already been "discovered" through a clause, if not, "discover" it
        	if(!inferred.containsKey(p)) {
        		inferred.put(p, true);
        		//If the literal appears in any clauses, decrease that clause's premises by 1
        		for(Map.Entry<CNFSubClause, Integer> c : count.entrySet()) {
        			if(c.getKey().getLiterals().contains(p)) {
        				count.put(c.getKey(), c.getValue()-1);
        				//If the clause's premises become 0, "activate" clause
        				if(c.getValue() == 0) {
        					//In order to find the inferred literal of a clause in Horn form we search for the only one that has a negation
        					for(Literal l : c.getKey().getLiterals()) {
        						if(!l.getNeg()) {
        							//If the inferred literal is our target, return true, otherwise add to our list of literals known to be true
        							if(l == q) {
        								return true;
        							}
        							if(!agenda.contains(l)) {
        								agenda.add(l);
        							}
        						}
        					}
        				}
        			}
        		}
        	}
        }
		return false;
	}

}
