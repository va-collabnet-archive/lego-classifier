package gov.va;

import gov.va.legoEdit.formats.LegoXMLUtils;
import gov.va.legoEdit.model.schemaModel.Lego;
import gov.va.legoEdit.model.schemaModel.LegoList;
import gov.va.legoEdit.model.sim.act.expression.ExpressionRelGroup;
import gov.va.legoEdit.model.sim.act.expression.node.ConjunctionNode;
import gov.va.legoEdit.storage.sim.util.SchemaToSimConversions;
import gov.va.sim.act.AssertionBI;
import gov.va.sim.act.expression.ExpressionRelBI;
import gov.va.sim.act.expression.ExpressionRelGroupBI;
import gov.va.sim.act.expression.node.BooleanNodeBI;
import gov.va.sim.act.expression.node.ConceptNodeBI;
import gov.va.sim.act.expression.node.ConjunctionNodeBI;
import gov.va.sim.act.expression.node.ExpressionNodeBI;
import gov.va.sim.act.expression.node.MeasurementNodeBI;
import gov.va.sim.act.expression.node.TextNodeBI;
import gov.va.sim.lego.LegoBI;
import gov.va.sim.measurement.BoundBI;
import gov.va.sim.measurement.IntervalBI;
import gov.va.sim.measurement.PointBI;
import java.io.File;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import org.ihtsdo.tk.api.concept.ConceptVersionBI;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import au.csiro.ontology.Factory;
import au.csiro.ontology.IOntology;
import au.csiro.ontology.Node;
import au.csiro.ontology.axioms.IAxiom;
import au.csiro.ontology.classification.IReasoner;
import au.csiro.ontology.model.IConcept;
import au.csiro.ontology.model.IConjunction;
import au.csiro.ontology.model.ILiteral;
import au.csiro.ontology.model.INamedFeature;
import au.csiro.ontology.model.INamedRole;
import au.csiro.ontology.model.Operator;
import au.csiro.snorocket.core.SnorocketReasoner;

/**
 * 
 * This is a rewrite of the initial "LegoClassifier" which operated directly using the Lego Schema model.
 * 
 * This classifer operates directly on the sim-api objects.  The main method still runs Legos through this
 * by converting them to sim-api.
 * 
 * @author Dan Armbrust
 */
public class SIMClassifier
{
	static Logger logger = LoggerFactory.getLogger(SIMClassifier.class);
	static String eol = System.getProperty("line.separator");
	IReasoner<String> reasoner;
	Factory<String> f = new Factory<>();
	Set<String> conceptIds = new HashSet<>();
	INamedRole<String> roleGroup = f.createRole("RoleGroup");
	HashSet<IAxiom> unclassifiedAxioms = new HashSet<>();

	public SIMClassifier(IReasoner<String> reasoner)
	{
		this.reasoner = reasoner;
	}

	public Set<IAxiom> getUnclassifiedAxioms()
	{
		return unclassifiedAxioms;
	}

	public void classifyAxioms()
	{
		reasoner.classify(unclassifiedAxioms);
		unclassifiedAxioms.clear();
	}

	public String getClassificationSummary()
	{
		StringBuilder sb = new StringBuilder();

		// The taxonomy contains the inferred hierarchy
		IOntology<String> t = reasoner.getClassifiedOntology();

		for (String s : conceptIds)
		{
			// We can look for nodes using the concept ids.
			Node<String> newNode = t.getNode(s);
			if (newNode == null)
			{
				sb.append("No Node " + s);
				sb.append(eol);
			}
			else
			{
				sb.append("Equivalent Concepts " + newNode.getEquivalentConcepts());
				sb.append(eol);

				// We can now look for the parent and child nodes
				Set<Node<String>> parentNodes = newNode.getParents();
				sb.append("Parents:");
				sb.append(eol);
				for (Node<String> parentNode : parentNodes)
				{
					sb.append("  " + parentNode.getEquivalentConcepts());
					sb.append(eol);
				}

				Set<Node<String>> childNodes = newNode.getChildren();
				sb.append("Children:");
				sb.append(eol);
				for (Node<String> childNode : childNodes)
				{
					sb.append("  " + childNode.getEquivalentConcepts());
					sb.append(eol);
				}
			}

			sb.append("=====================================");
			sb.append(eol);
		}
		return sb.toString();
	}
	
	public void convertToAxioms(LegoBI... legos) throws UnsupportedEncodingException, NoSuchAlgorithmException, IOException
	{
		for (LegoBI l : legos)
		{
			logger.debug("Converting Lego " + l.getInstanceUuid() + " to axioms");
			convertToAxioms(l.getAssertions().toArray(new AssertionBI[l.getAssertions().size()]));
		}
	}

	public void convertToAxioms(AssertionBI... assertions) throws UnsupportedEncodingException, NoSuchAlgorithmException, IOException
	{
		for (AssertionBI a : assertions)
		{
			// assertion components don't need classifying
			IConcept discernibleExpression = process(a.getDiscernable().getFocus());

			if (null != discernibleExpression && discernibleExpression instanceof IConjunction)
			{
				IConcept discernibleConcept = f.createConcept(a.getDiscernable().getUuid().toString());
				unclassifiedAxioms.add(f.createConceptInclusion(discernibleConcept, discernibleExpression));
				unclassifiedAxioms.add(f.createConceptInclusion(discernibleExpression, discernibleConcept));
			}

			IConcept qualifierExpression = process(a.getQualifier().getFocus());

			if (null != qualifierExpression && qualifierExpression instanceof IConjunction)
			{
				IConcept qualifierConcept = f.createConcept(a.getQualifier().getUuid().toString());
				unclassifiedAxioms.add(f.createConceptInclusion(qualifierConcept, qualifierExpression));
				unclassifiedAxioms.add(f.createConceptInclusion(qualifierExpression, qualifierConcept));
			}

			if (a.getValue().getFocus() == null)
			{
				throw new RuntimeException("Missing Value");
			}
			else if (a.getValue().getFocus() instanceof ConceptNodeBI || a.getValue().getFocus() instanceof ConjunctionNodeBI)
			{
				IConcept valueExpression = process(a.getValue().getFocus());

				if (null != valueExpression && valueExpression instanceof IConjunction)
				{
					IConcept valueConcept = f.createConcept(a.getValue().getUuid().toString());
					unclassifiedAxioms.add(f.createConceptInclusion(valueConcept, valueExpression));
					unclassifiedAxioms.add(f.createConceptInclusion(valueExpression, valueConcept));
				}
			}
			else if (a.getValue().getFocus() instanceof MeasurementNodeBI)
			{
				logger.debug("Value Measurements that are not part of an expression are not classified");
			}
			else if (a.getValue().getFocus() instanceof TextNodeBI)
			{
				logger.debug("Value text that is not part of an expression is not classified");
			}
			else if (a.getValue().getFocus() instanceof BooleanNodeBI)
			{
				logger.debug("Boolean value that is not part of an expression is not classified");
			}
			else
			{
				throw new RuntimeException("unexpected type '" + a.getValue().getFocus() + "' in Value");
			}

			if (a.getTiming() != null)
			{
				logger.debug("Timing information is not classified");
			}
		}
	}

	/**
	 * This method returns the right hand side of a concept inclusion axiom derived from an {@link ExpressionNodeBI<?>}.
	 * 
	 * @param expression
	 * @throws IOException 
	 */
	private IConcept process(ExpressionNodeBI<?> expression) throws IOException
	{
		// The list of conjuncts that will be returned
		List<IConcept> rhs = new ArrayList<IConcept>();

		// 1. Process the focus concept
		if (expression == null)
		{
			return null;
		}
		else if (expression instanceof ConceptNodeBI)
		{
			ConceptNodeBI cn = (ConceptNodeBI)expression;
			rhs.add(f.createConcept(cn.getConceptUuid().toString()));
		}
		else if (expression instanceof ConjunctionNode)
		{
			ConjunctionNode cn = (ConjunctionNode)expression;
			for (ExpressionNodeBI<?> e : cn.getValue())
			{
				rhs.add(process(e));
			}
		}
		else
		{
			throw new RuntimeException("unexpected case - missing expression?");
		}

		// 2. Process the relations

		// Build role groups
		HashMap<ExpressionRelGroupBI, Set<ExpressionRelBI>> relGroups = new HashMap<>();
		ExpressionRelGroup noGroup = new ExpressionRelGroup(null);
		relGroups.put(noGroup, new HashSet<ExpressionRelBI>()); 

		for (ExpressionRelBI rel : expression.getAllRels())
		{
			ExpressionRelGroupBI relGroup = rel.getRelGroup();
			if (relGroup == null)
			{
				relGroup = noGroup;
			}
			
			Set<ExpressionRelBI> relSet = relGroups.get(relGroup);
			if (relSet == null)
			{
				relSet = new HashSet<ExpressionRelBI>();
				relGroups.put(relGroup, relSet);
			}
			relGroups.get(relGroup).add(rel);
		}

		// Process relationships
		for (Entry<ExpressionRelGroupBI, Set<ExpressionRelBI>> relGroup : relGroups.entrySet())
		{
			if (relGroup.getKey() == noGroup)
			{
				// Special case - not grouped
				for (ExpressionRelBI r : relGroup.getValue())
				{
					IConcept temp = processRelationship(r);
					if (temp != null)
					{
						rhs.add(temp);
					}
				}
			}
			else
			{
				// All of these have to be grouped
				List<IConcept> conjs = new ArrayList<>();
				for (ExpressionRelBI r : relGroup.getValue())
				{
					IConcept temp = processRelationship(r);
					if (temp != null)
					{
						conjs.add(temp);
					}
				}
				IConcept rg = f.createExistential(roleGroup, f.createConjunction(conjs.toArray(new IConcept[conjs.size()])));
				rhs.add(rg);
			}
		}

		assert (!rhs.isEmpty());

		if (rhs.size() == 1)
		{
			return rhs.get(0);
		}
		else
		{
			return f.createConjunction(rhs.toArray(new IConcept[rhs.size()]));
		}
	}

	private IConcept processMeasurement(INamedFeature<String> feature, MeasurementNodeBI<?> measurement) throws IOException
	{
		IConcept unitsConcept = null;
		ConceptVersionBI conceptVersionBIUnits = getUnits(measurement); 
		if (conceptVersionBIUnits != null)
		{
			// units are optional
			unitsConcept = f.createConcept(conceptVersionBIUnits.getPrimUuid().toString());
		}
		
		IConcept data;
		if (measurement.getValue() instanceof PointBI)
		{
			PointBI p = (PointBI)measurement.getValue();
			data = processPoint(feature, p, Operator.EQUALS);
		}
		else if (measurement.getValue() instanceof BoundBI)
		{
			BoundBI b = (BoundBI)measurement.getValue();

			IConcept lower = null;
			IConcept upper = null;
			if (b.getLowerLimit() != null)
			{
				Operator lowerOperator = null;
				if (b.isLowerLimitInclusive())
				{
					lowerOperator = Operator.GREATER_THAN_EQUALS;
				}
				else
				{
					lowerOperator = Operator.GREATER_THAN;
				}
				lower = processPoint(feature, b.getLowerLimit(), lowerOperator);
			}

			if (b.getUpperLimit() != null)
			{
				Operator upperOperator = null;
				if (b.isUpperLimitInclusive())
				{
					upperOperator = Operator.LESS_THAN_EQUALS;
				}
				else
				{
					upperOperator = Operator.LESS_THAN;
				}
				upper = processPoint(feature, b.getUpperLimit(), upperOperator);
			}

			if (lower != null && upper != null)
			{
				data = f.createConjunction(lower, upper);
			}
			else if (lower != null)
			{
				data = lower;
			}
			else
			{
				data = upper;
			}
		}
		else if (measurement.getValue() instanceof IntervalBI)
		{
			IntervalBI i = (IntervalBI)measurement.getValue();

			// In the case of bounds, where we have an uncertainty range on each end of the interval - like this:
			// {[5] to (8)} <= X <= {(20) to [30]}
			// We turn this into [5] <= X <= [30] - as the classifier doesn't have a way to distinguish between definitely in the bound, and possibly
			// in the bound.
			// This will only allow querying if a point is in the interval but it will be impossible to know if it is either possibly
			// in the interval or definitively in the interval

			IConcept lower = null;
			IConcept upper = null;
			if (i.getLowerBound() != null && i.getLowerBound().getLowerLimit() != null)
			{
				Operator lowerOperator = null;
				if (i.getLowerBound().isLowerLimitInclusive())
				{
					lowerOperator = Operator.GREATER_THAN_EQUALS;
				}
				else
				{
					lowerOperator = Operator.GREATER_THAN;
				}
				lower = processPoint(feature, i.getLowerBound().getLowerLimit(), lowerOperator);
			}

			if (i.getUpperBound() != null && i.getUpperBound().getUpperLimit() != null)
			{
				Operator upperOperator = null;
				if (i.getUpperBound().isUpperLimitInclusive())
				{
					upperOperator = Operator.LESS_THAN_EQUALS;
				}
				else
				{
					upperOperator = Operator.LESS_THAN;
				}
				upper = processPoint(feature, i.getUpperBound().getUpperLimit(), upperOperator);
			}

			if (lower != null && upper != null)
			{
				data = f.createConjunction(lower, upper);
			}
			else if (lower != null)
			{
				data = lower;
			}
			else
			{
				data = upper;
			}
		}
		else
		{
			throw new RuntimeException("invalid measurement '" + measurement.getClass().getName() + "'");
		}
		
		if (unitsConcept != null)
		{
			// The units and datatype must be grouped
			IConcept conjunction = f.createConjunction(unitsConcept, data);
			return f.createExistential(roleGroup, conjunction);
		}
		else
		{
			return data;
		}
	}

	private IConcept processPoint(INamedFeature<String> feature, PointBI point, Operator operator)
	{
		IConcept data;
		
		if (point.getPointValue() instanceof Double || point.getPointValue() instanceof Float)
		{
			ILiteral literal = f.createDoubleLiteral(point.getPointValue().doubleValue());
			data = f.createDatatype(feature, operator, literal);
		}
		else
		{
			if (point.getPointValue().longValue() == Long.MIN_VALUE)
			{
				//TODO handle constants.... maybe I don't care.
				ILiteral literal = f.createStringLiteral("constant...");
				data = f.createDatatype(feature, operator, literal);
			}
			else
			{
				ILiteral literal = f.createLongLiteral(point.getPointValue().longValue());
				data = f.createDatatype(feature, operator, literal);
			}
		}
		return data;
	}
	
	private ConceptVersionBI getUnits(MeasurementNodeBI<?> measurement) throws IOException
	{
		//In SIM-API, each point has its own Units (optionally) but the classifier doesn't convert units, so we need to ensure they are all the same.
		//Then, since they are all the same, we will just put the units on the measurement, rather than on each point.
		
		if (measurement.getValue() instanceof PointBI)
		{
			return ((PointBI)measurement.getValue()).getUnitsOfMeasure();
		}
		else if (measurement.getValue() instanceof BoundBI)
		{
			return getUnits((BoundBI)measurement.getValue());
		}
		else if (measurement.getValue() instanceof IntervalBI)
		{
			ConceptVersionBI lowerUnits = getUnits(((IntervalBI)measurement.getValue()).getLowerBound());
			ConceptVersionBI upperUnits = getUnits(((IntervalBI)measurement.getValue()).getUpperBound());
			if (lowerUnits != null && upperUnits != null)
			{
				if (!lowerUnits.getPrimUuid().equals(upperUnits.getPrimUuid()))
				{
					throw new IOException("Units must be the same throughout a Measurement when they are provided.");
				}
				return lowerUnits;
			}
			else if (lowerUnits != null)
			{
				return lowerUnits;
			}
			else
			{
				return upperUnits;
			}
		}
		else
		{
			throw new IOException("Unsupported measurement type");
		}
	}
	
	private ConceptVersionBI getUnits(BoundBI bound) throws IOException
	{
		if (bound == null)
		{
			return null;
		}
		ConceptVersionBI units = null;
		if (bound.getLowerLimit() != null)
		{
			units = bound.getLowerLimit().getUnitsOfMeasure();
		}
		if (bound.getUpperLimit() != null)
		{
			if (units == null)
			{
				return bound.getUpperLimit().getUnitsOfMeasure();
			}
			else if (bound.getUpperLimit().getUnitsOfMeasure() != null)
			{
				if (!units.getPrimUuid().equals(bound.getUpperLimit().getUnitsOfMeasure().getPrimUuid()))
				{
					throw new IOException("Units must be the same throughout a Measurement when they are provided.");
				}
			}
		}
		return units;
	}

	private IConcept processRelationship(ExpressionRelBI r) throws IOException
	{
		// We need to determine if this relation refers to a role or a feature.
		// This is done by looking at the destination.
		ExpressionNodeBI<?> dest = r.getDestination();
		ConceptVersionBI tp = r.getType();

		if (dest instanceof ConjunctionNodeBI || dest instanceof ConceptNodeBI)
		{
			// If the destination is an expression the type is role
			INamedRole<String> role = f.createRole(tp.getPrimUuid().toString());
			IConcept destExpression = process(dest);
			return f.createExistential(role, destExpression);
		}
		else if (dest instanceof MeasurementNodeBI)
		{
			INamedFeature<String> feature = f.createFeature(tp.getPrimUuid().toString());
			IConcept measurementConcept = processMeasurement(feature, (MeasurementNodeBI<?>)dest);
			return measurementConcept;
		}
		else if (dest instanceof TextNodeBI)
		{
			INamedFeature<String> feature = f.createFeature(tp.getPrimUuid().toString());
			ILiteral literal = f.createStringLiteral(((TextNodeBI)dest).getValue());
			IConcept data = f.createDatatype(feature, Operator.EQUALS, literal);
			return data;
		}
		else if (dest instanceof BooleanNodeBI)
		{
			INamedFeature<String> feature = f.createFeature(tp.getPrimUuid().toString());
			ILiteral literal = f.createBooleanLiteral(((BooleanNodeBI)dest).getValue());
			IConcept data = f.createDatatype(feature, Operator.EQUALS, literal);
			return data;
		}
		else
		{
			throw new RuntimeException("invalid rel");
		}
	}

	public static void main(String[] args) throws UnsupportedEncodingException, NoSuchAlgorithmException, IOException
	{
		ArrayList<LegoBI> legos = new ArrayList<>();
		for (File f : new File("legos").listFiles())
		{
			if (f.exists() && f.isFile() && f.getName().toLowerCase().endsWith(".xml"))
			{
				try
				{
					LegoXMLUtils.validate((f));
					LegoList ll = LegoXMLUtils.readLegoList(f);
					logger.info("Reading " + f.getAbsolutePath());
					for (Lego l : ll.getLego())
					{
						legos.add(SchemaToSimConversions.convert(l));
					}
				}
				catch (Exception ex)
				{
					logger.error("Error reading file " + f.getName(), ex);
				}
			}
		}

		SIMClassifier lc = new SIMClassifier(new SnorocketReasoner<String>());
		lc.convertToAxioms(legos.toArray(new LegoBI[legos.size()]));

		System.out.println("******************************************");
		System.out.println("Converted Axioms");
		for (IAxiom axiom : lc.getUnclassifiedAxioms())
		{
			System.out.println(axiom);
		}
		System.out.println("******************************************");

		logger.info("Classifying Axioms");
		lc.classifyAxioms();
		logger.info("Done Classifying");

		logger.info("Classification Summary:");
		System.out.println(lc.getClassificationSummary());
	}
}
