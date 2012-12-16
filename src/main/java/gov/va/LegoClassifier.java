package gov.va;

import gov.va.legoSchema.Assertion;
import gov.va.legoSchema.Bound;
import gov.va.legoSchema.Concept;
import gov.va.legoSchema.Expression;
import gov.va.legoSchema.Interval;
import gov.va.legoSchema.Lego;
import gov.va.legoSchema.LegoList;
import gov.va.legoSchema.Measurement;
import gov.va.legoSchema.Point;
import gov.va.legoSchema.Relation;
import gov.va.legoSchema.RelationGroup;
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
            
            process("D", a.getDiscernible().getExpression());
            process("Q", a.getQualifier().getExpression());
            
            // Value
            if (a.getValue().getExpression() != null)
            {
                process("V", a.getValue().getExpression());
            }
            else if (a.getValue().getMeasurement() != null)
            {
                processMeasurement("Value", a.getValue().getMeasurement());
            }
            else if (a.getValue().getText() != null && a.getValue().getText().length() > 0)
            {
                ILiteral literal = f.createStringLiteral(a.getValue().getText());
                INamedFeature<String> feature = f.createFeature("ValueText:" + a.getValue().getText());
                f.createDatatype(feature, Operator.EQUALS, literal);
                //TODO do I need to do anything else with this text?
            }
            else if (a.getValue().isBoolean() != null)
            {
                ILiteral literal = f.createBooleanLiteral(a.getValue().isBoolean());
                INamedFeature<String> feature = f.createFeature("ValueBoolean:" + a.getValue().isBoolean());
                f.createDatatype(feature, Operator.EQUALS, literal);
                //TODO do I need to do anything else with this boolean?
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

    private IConcept process(String type, Expression dqvFocusExpression)
    {
        List<IConcept> rhs = new ArrayList<IConcept>();
        
        IConcept focusConcept;
        if (dqvFocusExpression == null)
        {
            return null;
        }
        else if (dqvFocusExpression.getConcept() != null)
        {
            focusConcept = f.createConcept(getIdForConcept(dqvFocusExpression.getConcept()));
        }
        else if (dqvFocusExpression.getExpression().size() > 0)
        {
            List<IConcept> conjunctionConcepts = new ArrayList<IConcept>(dqvFocusExpression.getExpression().size());
            for (Expression e : dqvFocusExpression.getExpression())
            {
                conjunctionConcepts.add(process(type, e));
            }
            focusConcept = f.createConjunction(conjunctionConcepts.toArray(new IConcept[conjunctionConcepts.size()]));
            
            IConcept conjunctionEquivConcept = f.createConcept(generateUUID(type, dqvFocusExpression.getExpression().toArray(new Expression[0])));
            
            axioms.add(f.createConceptInclusion(conjunctionEquivConcept, focusConcept));
            axioms.add(f.createConceptInclusion(focusConcept, conjunctionEquivConcept));
        }
        else
        {
            throw new RuntimeException("unexpected case");
        }
        
        if (dqvFocusExpression.getRelation() != null)
        {
            for (Relation r : dqvFocusExpression.getRelation())
            {
                IConcept temp = createExistential(type, r);
                if (temp != null)
                {
                    rhs.add(temp);
                }
            }
        }
        if (dqvFocusExpression.getRelationGroup() != null)
        {
            int relationGroupID = 1;
            for (RelationGroup rg : dqvFocusExpression.getRelationGroup())
            {
                List<IConcept> roleGroupMembers = new ArrayList<IConcept>();
                for (Relation r : rg.getRelation())
                {
                    //TODO figure out a way to generate a proper ID for the relationGroup...
                    IConcept temp = createExistential(type, r);
                    if (temp != null)
                    {
                        roleGroupMembers.add(temp);
                    }
                }
                if (roleGroupMembers.size() > 0)
                {
                    IConcept roleMembers = f.createConjunction(roleGroupMembers.toArray(new IConcept[roleGroupMembers.size()]));
                    IConcept equivConcept = f.createConcept(generateUUID(rg.getRelation().toArray(new Relation[0])));
                    axioms.add(f.createConceptInclusion(equivConcept, roleMembers));
                    axioms.add(f.createConceptInclusion(roleMembers, equivConcept));
                    
                    IConcept roleGroup = f.createExistential(f.createRole("RoleGroup" + relationGroupID++), roleMembers);
                    rhs.add(roleGroup);
                }
            }
        }
        
        if (rhs.size() > 0)
        {
            rhs.add(0, focusConcept);
            IConcept conjunction = f.createConjunction(rhs.toArray(new IConcept[rhs.size()]));
            
            IConcept equivConcept = f.createConcept(generateUUID(type, new Expression[] {dqvFocusExpression}));
            
            axioms.add(f.createConceptInclusion(equivConcept, conjunction));
            axioms.add(f.createConceptInclusion(conjunction, equivConcept));
            return conjunction;
        }
        else
        {
            return focusConcept;
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
        
        IConcept data;
        String dataId;
        
        if (m.getPoint() != null)
        {
            //TODO no idea if this measurement processing is right
            Point p = m.getPoint();
            if (p.getNumericValue() != null)
            {
                //TODO 1 point will always be inclusive, however if point is part of an interval, then maybe not, need to break point processing out
//                boolean inclusive;
//                if (p.isInclusive() == null)
//                {
//                    inclusive = true;
//                }
//                else
//                {
//                    inclusive = p.isInclusive().booleanValue();
//                }
                
                ILiteral literal = f.createDoubleLiteral(p.getNumericValue());
                
                INamedFeature<String> feature = f.createFeature("equals:" + p.getNumericValue());
                data = f.createDatatype(feature, Operator.EQUALS, literal);
                dataId = ":equals:" + p.getNumericValue();
            }
            else if (p.getStringConstant() != null)
            {
                ILiteral literal = f.createStringLiteral(p.getStringConstant().name());
                INamedFeature<String> feature = f.createFeature("MeasurementConstant:" + p.getStringConstant().name());
                data = f.createDatatype(feature, Operator.EQUALS, literal);
                dataId = ":equals:" + p.getStringConstant().name();
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
        
        if (unitsConcept != null)
        {
            IConcept conjunction = f.createConjunction(unitsConcept, data);
            IConcept equivConcept = f.createConcept(type + ":" + getIdForConcept(m.getUnits().getConcept()) + dataId);
            axioms.add(f.createConceptInclusion(equivConcept, conjunction));
            axioms.add(f.createConceptInclusion(conjunction, equivConcept));
            return conjunction;
        }
        else
        {
            return data;
        }
    }
    

    private IConcept createExistential(String type, Relation r)
    {
        INamedRole<String> typeConcept = f.createRole(getValuesInConcept(r.getType().getConcept()));
        if (r.getDestination().getExpression() != null)
        {
            IConcept destExpression = process(type + "Rel", r.getDestination().getExpression()); 
            return f.createExistential(typeConcept, destExpression);
        }
        else if (r.getDestination().getMeasurement() != null)
        {
            IConcept measurementConcept = processMeasurement("Destination", r.getDestination().getMeasurement());
            return f.createExistential(typeConcept, measurementConcept);
        }
        else if (r.getDestination().getText() != null && r.getDestination().getText().length() > 0)
        {
            ILiteral literal = f.createStringLiteral(r.getDestination().getText());
            INamedFeature<String> feature = f.createFeature("DestinationText:" + r.getDestination().getText());
            IConcept data = f.createDatatype(feature, Operator.EQUALS, literal);
            return f.createExistential(typeConcept, data);
        }
        else if (r.getDestination().isBoolean() != null)
        {
            ILiteral literal = f.createBooleanLiteral(r.getDestination().isBoolean());
            INamedFeature<String> feature = f.createFeature("DestinationBoolean:" + r.getDestination().isBoolean());
            IConcept data = f.createDatatype(feature, Operator.EQUALS, literal);
            return f.createExistential(typeConcept, data);
        }
        else
        {
            throw new RuntimeException("invalid rel");
        }
    }
    
    /**
     * Generate a unique ID based off of the relations (and all subconcepts)
     */
    private String generateUUID(Relation[] relations)
    {
        //TODO not sure if this ID is being generated correctly - what should the ID represent?
        StringBuilder sb = new StringBuilder();
        for (Relation r : relations)
        {
            buildIDComponents(sb, r);
        }
        UUID uuid = UUID.nameUUIDFromBytes(sb.toString().getBytes());
        logger.debug("Created " + uuid.toString() + " from " + sb.toString());
        conceptIds.add(uuid.toString());
        return uuid.toString();
    }

    
    /**
     * Generate a unique ID based off of the expressions (and all subconcepts)
     */
    private String generateUUID(String type, Expression[] expressions)
    {
        //TODO not sure if this ID is being generated correctly - what should the ID represent?
        StringBuilder sb = new StringBuilder();
        sb.append(type);
        for (Expression e : expressions)
        {
            buildIDComponents(sb, e);
        }
        UUID uuid = UUID.nameUUIDFromBytes(sb.toString().getBytes());
        logger.debug("Created " + uuid.toString() + " from " + sb.toString());
        conceptIds.add(uuid.toString());
        return uuid.toString();
    }
    
    private void buildIDComponents(StringBuilder sb, Expression expression)
    {
        sb.append(":");
        if (expression.getConcept() != null)
        {
            sb.append(getValuesInConcept(expression.getConcept()));
        }
        else if(expression.getExpression().size() > 0)
        {
            for (Expression e : expression.getExpression())
            {
                buildIDComponents(sb, e);
            }
        }
        else
        {
            throw new RuntimeException("unexpected case");
        }
        
        if (expression.getRelation() != null)
        {
            for (Relation r : expression.getRelation())
            {
                buildIDComponents(sb, r);
            }
        }
        if (expression.getRelationGroup() != null)
        {
            int i = 1;
            for (RelationGroup rg : expression.getRelationGroup())
            {
                //TODO better identifiers for RoleGroup
                sb.append(":RG" + i++);
                for (Relation r : rg.getRelation())
                {
                    sb.append(":i");
                    buildIDComponents(sb, r);
                }
            }
        }
    }
    
    private void buildIDComponents(StringBuilder sb, Relation r)
    {
        buildIDComponents(sb, r.getType().getConcept());
        if (r.getDestination().getExpression() != null)
        {
            buildIDComponents(sb, r.getDestination().getExpression());
        }
        else if (r.getDestination().getMeasurement() != null)
        {
            if (r.getDestination().getMeasurement().getUnits() != null)
            {
                buildIDComponents(sb, r.getDestination().getMeasurement().getUnits().getConcept());
            }
            sb.append(getValuesInInterval(r.getDestination().getMeasurement().getInterval()));
            sb.append(getValueInPoint(r.getDestination().getMeasurement().getPoint()));
        }
        else if (r.getDestination().getText() != null && r.getDestination().getText().length() > 0)
        {
            sb.append(r.getDestination().getText());
        }
        else if (r.getDestination().isBoolean() != null)
        {
            sb.append(r.getDestination().isBoolean());
        }
    }
    
    private void buildIDComponents(StringBuilder sb, Concept c)
    {
        sb.append(":");
        sb.append(getIdForConcept(c));
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
            return ":" + p.getStringConstant().name();
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
