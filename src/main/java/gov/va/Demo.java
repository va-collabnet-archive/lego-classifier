/**
 * Copyright CSIRO Australian e-Health Research Centre (http://aehrc.com).
 * All rights reserved. Use is subject to license terms and conditions.
 */
package gov.va;


import gov.va.legoEdit.formats.LegoXMLUtils;
import gov.va.legoEdit.model.schemaModel.Lego;
import gov.va.legoEdit.model.schemaModel.LegoList;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import javax.xml.bind.JAXBException;
import au.csiro.ontology.IOntology;
import au.csiro.ontology.Node;
import au.csiro.ontology.axioms.IAxiom;
import au.csiro.ontology.axioms.IConceptInclusion;
import au.csiro.ontology.classification.IReasoner;
import au.csiro.ontology.model.INamedConcept;
import au.csiro.snorocket.core.SnorocketReasoner;
import au.csiro.snorocket.core.util.Utils;

/**
 * Demo class for the final webinar. Shows how to load the base state for the
 * classifier and how to run an incremental classification with a Lego.
 * 
 * @author Alejandro Metke
 *
 */
public class Demo {

public Demo() {
        
    }
    
    @SuppressWarnings("unchecked")
    public void start() throws FileNotFoundException, JAXBException {
        
        // 1. Load the base state
    	System.out.println("Loading base state from classifier_uuid.state");
        IReasoner<String> reasoner = SnorocketReasoner.load(
                this.getClass().getResourceAsStream("/classifier_uuid.state"));
        
        // 2. Load SCT to UUID map
        System.out.println("Loading uuid description map");
        Map<String, String> sctToUuidMap = new HashMap<>();
        Map<String, String> uuidToDescMap = new HashMap<>();
        try (BufferedReader reader = new BufferedReader(new InputStreamReader(
                this.getClass().getResourceAsStream("/nid_sctid_uuid_map.txt"), 
                StandardCharsets.UTF_8))) {
            String line = null;
            while ((line = reader.readLine()) != null) {
                String[] parts = line.split("[,]");
                String desc = "";
                if(parts.length == 4) {
                    desc = parts[3];
                }
                if(parts[1].equals("NA")) continue;
                sctToUuidMap.put(parts[1], parts[2]);
                uuidToDescMap.put(parts[2], desc);
            }      
        } catch (IOException e) {
            e.printStackTrace();
            return;
        }
        
        // 2. Load Lego
        System.out.println(
        		"Transforming Pressure ulcer observables lego into axioms");
        ArrayList<Lego> legos = new ArrayList<Lego>();
        LegoList ll = LegoXMLUtils.readLegoList(
        		this.getClass().getResourceAsStream(
        				"/Nested.xml"));
        for (Lego l : ll.getLego()) {
            legos.add(l);
        }
        
        LegoClassifier lc = new LegoClassifier(reasoner);        
        lc.convertToAxioms(legos.toArray(new Lego[legos.size()]));

        // Extract the UUIDs for the Assertions 
        final Set<String> assertionUUIDs = new HashSet<>();
        for (IAxiom axiom: lc.getUnclassifiedAxioms()) {
        	if (axiom instanceof IConceptInclusion) {
        		IConceptInclusion ci = (IConceptInclusion) axiom;
        		if (ci.lhs() instanceof INamedConcept<?>) {
        			assertionUUIDs.add(((INamedConcept<String>) ci.lhs()).getId());
        		}
        	}
        }
        
        // 3. Classify incrementally
        System.out.println("Classifying incrementally");
        lc.classifyAxioms();
        
        // 4. Retrieve taxonomy
        System.out.println("Retrieving taxonomy");
        IOntology<String> ont = reasoner.getClassifiedOntology();
        
        for (String id: assertionUUIDs) {
        	// 5. Get node for new concept
        	Node<String> newNode = ont.getNodeMap().get(id);

        	// 6. Print the new node
        	for(Node<String> node : newNode.getParents()) {
        		Utils.printTaxonomy(
        			node, 
        			ont.getBottomNode(), 
        			uuidToDescMap
        		);
        	}
        }
    }
    
    /**
     * @param args
     */
    public static void main(String[] args) {
        Demo d = new Demo();
        
        try {
			d.start();
		} catch (FileNotFoundException | JAXBException e) {
			e.printStackTrace();
		}
    }

}
