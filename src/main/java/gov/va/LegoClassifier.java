package gov.va;

import gov.va.legoSchema.Assertion;
import gov.va.legoSchema.Bound;
import gov.va.legoSchema.Concept;
import gov.va.legoSchema.Interval;
import gov.va.legoSchema.Lego;
import gov.va.legoSchema.LegoList;
import gov.va.legoSchema.Point;
import gov.va.legoSchema.Rel;
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
import au.csiro.ontology.model.INamedRole;
import au.csiro.snorocket.core.SnorocketReasoner;

public class LegoClassifier
{
    Logger logger = LoggerFactory.getLogger(LegoClassifier.class);

    IReasoner<String> reasoner = new SnorocketReasoner<>();
    Factory<String> f = new Factory<>();
    Set<String> assertionIds = new HashSet<>();

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
        
        // The taxonomy contains the inferred hierarchy
        IOntology<String> t = reasoner.getClassifiedOntology();

        for (String s : assertionIds)
        {
            // We can look for nodes using the concept ids.
            Node<String> newNode = t.getNode(s);
            if (newNode == null)
            {
                //some still fail at the moment
                continue;
            }
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
            
            System.out.println("=====================================");
        }
    }

    private void classify(Lego l)
    {
        Set<IAxiom> axioms = new HashSet<>();

        for (Assertion a : l.getAssertion())
        {
            // TODO assertion components
            // TODO timings
            // TODO IConcept per assertion, or one IConcept per lego?
            // TODO how often to call classify? Once per lego?

            String id = generateUUID(a);
            assertionIds.add(id);
            IConcept assertionConcept = f.createConcept(id);

            // Discernibile
            process(axioms, a.getDiscernible().getConcept(), assertionConcept);

            // Qualifier
            process(axioms, a.getQualifier().getConcept(), assertionConcept);

            // Value
            if (a.getValue().getConcept() != null)
            {
                process(axioms, a.getValue().getConcept(), assertionConcept);
            }
            else
            {
                logger.error("value measurements not supported yet");
                continue;
            }
        }
        reasoner.classify(axioms);
    }

    private void process(Set<IAxiom> axioms, Concept dqvFocusConcept, IConcept assertionConcept)
    {
        IConcept focusConcept = f.createConcept(getValuesInConcept(dqvFocusConcept));
        
        if (dqvFocusConcept.getRel() != null)
        {
            List<IConcept> rhs = new ArrayList<IConcept>();
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
                IConcept conjunction = f.createConjunction(rhs.toArray(new IConcept[0]));
                axioms.add(f.createConceptInclusion(assertionConcept, conjunction));
                axioms.add(f.createConceptInclusion(conjunction, assertionConcept));
            }
            else
            {
                axioms.add(f.createConceptInclusion(assertionConcept, focusConcept));
                axioms.add(f.createConceptInclusion(focusConcept, assertionConcept));
            }
        }
        else
        {
            axioms.add(f.createConceptInclusion(assertionConcept, focusConcept));
            axioms.add(f.createConceptInclusion(focusConcept, assertionConcept));
        }
    }

    private IConcept createExistential(Rel r)
    {
        INamedRole<String> typeConcept = f.createRole(getValuesInConcept(r.getType().getConcept()));
        // TODO handle nested concepts under type and dest
        if (r.getDestination().getConcept() != null)
        {
            IConcept destConcept = f.createConcept(getValuesInConcept(r.getDestination().getConcept()));
            return f.createExistential(typeConcept, destConcept);
        }
        else
        {
            logger.error("measurement destinations not yet handeled");
            return null;
        }
    }

    /**
     * Generate a unique ID based off of the concept (and all subconcepts)
     */
    private String generateUUID(Assertion a)
    {
        StringBuilder sb = new StringBuilder();
        buildIDComponents(sb, a.getDiscernible().getConcept());
        buildIDComponents(sb, a.getQualifier().getConcept());
        if (a.getValue().getConcept() != null)
        {
            buildIDComponents(sb, a.getValue().getConcept());
        }
        else
        {
            sb.append(getValuesInInterval(a.getValue().getMeasurement().getInterval()));
            sb.append(getValueInPoint(a.getValue().getMeasurement().getPoint()));
        }
        UUID uuid = UUID.nameUUIDFromBytes(sb.toString().getBytes());
        logger.debug("Created " + uuid.toString() + " from " + sb.toString());
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

    private String getValuesInConcept(Concept c)
    {
        if (c.getSctid() != null)
        {
            return c.getSctid().toString();
        }
        else
        {
            return c.getUuid();
        }
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
