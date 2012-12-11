package gov.va;

import gov.va.legoSchema.Assertion;
import gov.va.legoSchema.Bound;
import gov.va.legoSchema.Concept;
import gov.va.legoSchema.Interval;
import gov.va.legoSchema.Lego;
import gov.va.legoSchema.LegoList;
import gov.va.legoSchema.Measurement;
import gov.va.legoSchema.Point;
import gov.va.legoSchema.Rel;
import gov.va.legoSchema.Timing;
import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.UUID;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import au.csiro.ontology.Factory;
import au.csiro.ontology.IOntology;
import au.csiro.ontology.Node;
import au.csiro.ontology.axioms.IAxiom;
import au.csiro.ontology.classification.IReasoner;
import au.csiro.ontology.model.IConcept;
import au.csiro.ontology.model.ILiteral;
import au.csiro.ontology.model.INamedFeature;
import au.csiro.ontology.model.INamedRole;
import au.csiro.ontology.model.Operator;
import au.csiro.snorocket.core.SnorocketReasoner;

public class LegoClassifier
{
    Logger logger = LoggerFactory.getLogger(LegoClassifier.class);

    IReasoner<String> reasoner = new SnorocketReasoner<>();
    Factory<String> f = new Factory<>();
    Set<String> conceptIds = new HashSet<>();
    Set<IAxiom> axioms = new HashSet<>();

    public LegoClassifier()
    {
        for (File f : new File("legos").listFiles())
        {

            if (f.exists() && f.isFile() && f.getName().toLowerCase().endsWith(".xml"))
            {
                try
                {
                    LegoXMLUtils.validate((f));
                    LegoList ll = LegoXMLUtils.readLegoList(f);
                    logger.info("Processing " + f.getAbsolutePath());
                    for (Lego l : ll.getLego())
                    {
                        classify(l);
                    }

                }
                catch (Exception ex)
                {
                    logger.error("Error processing file " + f.getName(), ex);
                }
            }
        }
        
        reasoner.classify(axioms);
        
        // The taxonomy contains the inferred hierarchy
        IOntology<String> t = reasoner.getClassifiedOntology();

        for (String s : conceptIds)
        {
            // We can look for nodes using the concept ids.
            Node<String> newNode = t.getNode(s);
            if (newNode == null)
            {
                System.out.println("No Node " + s);
            }
            else
            {
                System.out.println("Equivalent Concepts " + newNode.getEquivalentConcepts());
    
                // We can now look for the parent and child nodes
                Set<Node<String>> parentNodes = newNode.getParents();
                System.out.println("Parents:");
                for (Node<String> parentNode : parentNodes)
                {
                    System.out.println("  " + parentNode.getEquivalentConcepts());
                }
    
                Set<Node<String>> childNodes = newNode.getChildren();
                System.out.println("Children:");
                for (Node<String> childNode : childNodes)
                {
                    System.out.println("  " + childNode.getEquivalentConcepts());
                }
            }
            
            System.out.println("=====================================");
        }
    }

    private void classify(Lego l)
    {
        for (Assertion a : l.getAssertion())
        {
            // TODO assertion components
            // TODO do I have to do the equivalence thing whenever I make a conjunction? 
            
            // Discernibile
            if (a.getDiscernible().getConcept() != null)
            {
                process("D", a.getDiscernible().getConcept());
            }
            else if (false)
            {
                //TODO conjunction
            }

            // Qualifier
            if (a.getQualifier().getConcept() != null)
            {
                process("Q", a.getQualifier().getConcept());
            }
            else if (false)
            {
                //TODO conjunction
            }

            // Value
            if (a.getValue().getConcept() != null)
            {
                process("V", a.getValue().getConcept());
            }
            else if (false)
            {
                //TODO conjunction
            }
            else if (a.getValue().getMeasurement() != null)
            {
                processMeasurement("Value", a.getValue().getMeasurement());
            }
            
            //Timing
            if (a.getTiming() != null)
            {
                Timing t = a.getTiming();
                Measurement m = t.getMeasurement();
                if (m != null)
                {
                    processMeasurement("Timing", m);
                }
            }
        }
    }

    private void process(String type, Concept dqvFocusConcept)
    {
        List<IConcept> rhs = new ArrayList<IConcept>();
        IConcept focusConcept = f.createConcept(getIdForConcept(dqvFocusConcept)); 
        if (dqvFocusConcept.getRel() != null)
        {
            for (Rel r : dqvFocusConcept.getRel())
            {
                IConcept temp = createExistential(r);
                if (temp != null)
                {
                    rhs.add(temp);
                }
            }
            if (rhs.size() > 0)
            {
                rhs.add(0, focusConcept);
                IConcept conjunction = f.createConjunction(rhs.toArray(new IConcept[rhs.size()]));
                
                //TODO not sure if this ID is being generated correctly
                IConcept equivConcept = f.createConcept(generateUUID(type, dqvFocusConcept));
                
                axioms.add(f.createConceptInclusion(equivConcept, conjunction));
                axioms.add(f.createConceptInclusion(conjunction, equivConcept));
            }
        }
    }
    
    private IConcept processMeasurement(String type, Measurement m)
    {
        IConcept unitsConcept = null;
        if (m.getUnits() != null && m.getUnits().getConcept() != null)
        {
            //units are optional
            unitsConcept = f.createConcept(getIdForConcept(m.getUnits().getConcept()));
        }
        
        if (m.getPoint() != null)
        {
            //TODO no idea if this measurement processing is right
            Point p = m.getPoint();
            if (p.getNumericValue() != null)
            {
                boolean inclusive;
                if (p.isInclusive() == null)
                {
                    inclusive = true;
                }
                else
                {
                    inclusive = p.isInclusive().booleanValue();
                }
                
                ILiteral literal = f.createDoubleLiteral(p.getNumericValue());
                
                INamedFeature<String> feature = f.createFeature("equals:" + p.getNumericValue());
                IConcept data = f.createDatatype(feature, Operator.EQUALS, literal);
                
                if (unitsConcept != null)
                {
                    IConcept conjunction = f.createConjunction(unitsConcept, data);
                    IConcept equivConcept = f.createConcept(type + ":" + getIdForConcept(m.getUnits().getConcept()) + ":equals:" + p.getNumericValue());
                    axioms.add(f.createConceptInclusion(equivConcept, conjunction));
                    axioms.add(f.createConceptInclusion(conjunction, equivConcept));
                    return conjunction;
                }
                else
                {
                    return data;
                }
            }
            else if (p.getStringValue() != null)
            {
                //TODO string constant
                throw new RuntimeException("string value not yet handled in measurement");
            }
            else
            {
                throw new RuntimeException("invalid measurement");
            }
        }
        else if (m.getInterval() != null)
        {
            //TODO interval
            throw new RuntimeException("measurement interval not yet handeled");
        }
        else
        {
            throw new RuntimeException("invalid measurement");
        }
    }
    

    private IConcept createExistential(Rel r)
    {
        //TODO - type is (maybe) not supposed to support nested concepts... not sure - still waiting confirmation.
        INamedRole<String> typeConcept = f.createRole(getValuesInConcept(r.getType().getConcept()));
        if (r.getDestination().getConcept() != null)
        {
            IConcept destConcept = f.createConcept(getIdForConcept(r.getDestination().getConcept()));
            
            ArrayList<IConcept> nestedExistentials = new ArrayList<IConcept>();
            if (r.getDestination().getConcept().getRel() != null)
            {
                for (Rel nestedRel : r.getDestination().getConcept().getRel())
                {
                    nestedExistentials.add(createExistential(nestedRel));
                }
            }
            
            if (nestedExistentials.size() > 0)
            {
                nestedExistentials.add(0, destConcept);
                return f.createExistential(typeConcept, f.createConjunction(nestedExistentials.toArray(new IConcept[0])));
            }
            else
            {
                return f.createExistential(typeConcept, destConcept);
            }
        }
        else if (r.getDestination().getMeasurement() != null)
        {
            IConcept measurementConcept = processMeasurement("Destination", r.getDestination().getMeasurement());
            return f.createExistential(typeConcept, measurementConcept);
        }
        else
        {
            throw new RuntimeException("invalid rel");
        }
    }

    /**
     * Generate a unique ID based off of the concept (and all subconcepts)
     */
    private String generateUUID(String type, Concept c)
    {
        StringBuilder sb = new StringBuilder();
        sb.append(type);
        buildIDComponents(sb, c);
        UUID uuid = UUID.nameUUIDFromBytes(sb.toString().getBytes());
        logger.debug("Created " + uuid.toString() + " from " + sb.toString());
        conceptIds.add(uuid.toString());
        return uuid.toString();
    }

    private void buildIDComponents(StringBuilder sb, Concept expression)
    {
        sb.append(":");
        sb.append(getValuesInConcept(expression));
        if (expression.getRel() != null)
        {
            for (Rel r : expression.getRel())
            {
                buildIDComponents(sb, r.getType().getConcept());
                if (r.getDestination().getConcept() != null)
                {
                    buildIDComponents(sb, r.getDestination().getConcept());
                }
                else
                {
                    if (r.getDestination().getMeasurement().getUnits() != null)
                    {
                        buildIDComponents(sb, r.getDestination().getMeasurement().getUnits().getConcept());
                    }
                    sb.append(getValuesInInterval(r.getDestination().getMeasurement().getInterval()));
                    sb.append(getValueInPoint(r.getDestination().getMeasurement().getPoint()));
                }
            }
        }
    }
    
    private String getIdForConcept(Concept c)
    {
        String s = getValuesInConcept(c);
        conceptIds.add(s);
        return s;
    }

    private String getValuesInConcept(Concept c)
    {
        String conceptId = null;
        if (c.getSctid() != null)
        {
            conceptId = c.getSctid().toString(); 
        }
        else
        {
            conceptId = c.getUuid();
        }
        return conceptId;
    }

    private String getValuesInInterval(Interval i)
    {
        if (i == null)
        {
            return "";
        }
        else
        {
            return getValuesInBound(i.getLowerBound()) + getValuesInBound(i.getUpperBound())
                    + getValueInPoint(i.getLowerPoint()) + getValueInPoint(i.getUpperPoint());
        }
    }

    private String getValuesInBound(Bound b)
    {
        if (b == null)
        {
            return "";
        }
        else
        {
            return getValueInPoint(b.getLowerPoint()) + getValueInPoint(b.getUpperPoint());
        }
    }

    private String getValueInPoint(Point p)
    {
        if (p == null)
        {
            return "";
        }
        else if (p.getNumericValue() != null)
        {
            return ":" + p.getNumericValue();
        }
        else
        {
            return ":" + p.getStringValue().name();
        }
    }

    /**
     * @param args
     */
    public static void main(String[] args)
    {
        new LegoClassifier();
    }
}
