package gov.va;

import gov.va.legoEdit.formats.LegoXMLUtils;
import gov.va.legoEdit.model.schemaModel.Assertion;
import gov.va.legoEdit.model.schemaModel.Bound;
import gov.va.legoEdit.model.schemaModel.Concept;
import gov.va.legoEdit.model.schemaModel.Destination;
import gov.va.legoEdit.model.schemaModel.Expression;
import gov.va.legoEdit.model.schemaModel.Interval;
import gov.va.legoEdit.model.schemaModel.Lego;
import gov.va.legoEdit.model.schemaModel.LegoList;
import gov.va.legoEdit.model.schemaModel.Measurement;
import gov.va.legoEdit.model.schemaModel.Point;
import gov.va.legoEdit.model.schemaModel.PointDouble;
import gov.va.legoEdit.model.schemaModel.PointLong;
import gov.va.legoEdit.model.schemaModel.PointMeasurementConstant;
import gov.va.legoEdit.model.schemaModel.Relation;
import gov.va.legoEdit.model.schemaModel.RelationGroup;
import gov.va.legoEdit.model.schemaModel.Type;
import java.io.File;
import java.io.UnsupportedEncodingException;
import java.security.InvalidParameterException;
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
import au.csiro.ontology.model.IConjunction;
import au.csiro.ontology.model.ILiteral;
import au.csiro.ontology.model.INamedFeature;
import au.csiro.ontology.model.INamedRole;
import au.csiro.ontology.model.Operator;
import au.csiro.snorocket.core.SnorocketReasoner;

/**
 * Note - this class was a first attempt - and it not entirely correct in the way that it generates identifiers.
 * You really should be using the SIMClassifier class now. 
 * 
 * @author Dan Armbrust
 * @author Alejandro Metke
 */
public class LegoClassifier
{
	static Logger logger = LoggerFactory.getLogger(LegoClassifier.class);
	static String eol = System.getProperty("line.separator");
	IReasoner<String> reasoner;
	Factory<String> f = new Factory<>();
	Set<String> conceptIds = new HashSet<>();
	INamedRole<String> roleGroup = f.createRole("RoleGroup");
	HashSet<IAxiom> unclassifiedAxioms = new HashSet<>();

	public LegoClassifier(IReasoner<String> reasoner)
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

	public void convertToAxioms(Lego... legos)
	{
		for (Lego l : legos)
		{
			logger.debug("Converting Lego " + l.getLegoUUID() + " to axioms");
			for (Assertion a : l.getAssertion())
			{
				// assertion components don't need classifying
				IConcept discernibleExpression = process(a.getDiscernible().getExpression());

				if (null != discernibleExpression && discernibleExpression instanceof IConjunction)
				{
					String id = generateUUID(a.getDiscernible().getExpression());
					IConcept discernibleConcept = f.createConcept(id);
					unclassifiedAxioms.add(f.createConceptInclusion(discernibleConcept, discernibleExpression));
					unclassifiedAxioms.add(f.createConceptInclusion(discernibleExpression, discernibleConcept));
				}

				IConcept qualifierExpression = process(a.getQualifier().getExpression());

				if (null != qualifierExpression && qualifierExpression instanceof IConjunction)
				{
					String id = generateUUID(a.getQualifier().getExpression());
					IConcept qualifierConcept = f.createConcept(id);
					unclassifiedAxioms.add(f.createConceptInclusion(qualifierConcept, qualifierExpression));
					unclassifiedAxioms.add(f.createConceptInclusion(qualifierExpression, qualifierConcept));
				}

				if (a.getValue().getExpression() != null)
				{
					IConcept valueExpression = process(a.getValue().getExpression());

					if (null != valueExpression && valueExpression instanceof IConjunction)
					{
						String id = generateUUID(a.getValue().getExpression());
						IConcept valueConcept = f.createConcept(id);
						unclassifiedAxioms.add(f.createConceptInclusion(valueConcept, valueExpression));
						unclassifiedAxioms.add(f.createConceptInclusion(valueExpression, valueConcept));
					}
				}
				else if (a.getValue().getMeasurement() != null)
				{
					logger.debug("Value Measurements that are not part of an expression are not classified");
				}
				else if (a.getValue().getText() != null && a.getValue().getText().length() > 0)
				{
					logger.debug("Value text that is not part of an expression is not classified");
				}
				else if (a.getValue().isBoolean() != null)
				{
					logger.debug("Boolean value that is not part of an expression is not classified");
				}
				else
				{
					throw new RuntimeException("Missing value?");
				}

				if (a.getTiming() != null)
				{
					logger.debug("Timing information is not classified");
				}
			}
		}
	}

	/**
	 * This method returns the right hand side of a concept inclusion axiom derived from an {@link Expression}.
	 * 
	 * @param expression
	 */
	private IConcept process(Expression expression)
	{
		// The list of conjuncts that will be returned
		List<IConcept> rhs = new ArrayList<IConcept>();

		// 1. Process the focus concept
		if (expression == null)
		{
			return null;
		}
		else if (expression.getConcept() != null)
		{
			rhs.add(f.createConcept(getIdForConcept(expression.getConcept())));
		}
		else if (expression.getExpression().size() > 0)
		{
			for (Expression e : expression.getExpression())
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
		List<Set<Relation>> relGroups = new ArrayList<>();
		relGroups.add(new HashSet<Relation>()); // group 0
		// Put ungrouped relations to group 0
		relGroups.get(0).addAll(expression.getRelation());

		for (RelationGroup rg : expression.getRelationGroup())
		{
			relGroups.add(new HashSet<Relation>(rg.getRelation()));
		}

		// Process relationships
		for (int i = 0; i < relGroups.size(); i++)
		{
			Set<Relation> relGroup = relGroups.get(i);
			if (i == 0)
			{
				// Special case - not grouped
				for (Relation r : relGroup)
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
				for (Relation r : relGroup)
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

	private IConcept processMeasurement(INamedFeature<String> feature, Measurement measurement)
	{
		IConcept unitsConcept = null;
		if (measurement.getUnits() != null && measurement.getUnits().getConcept() != null)
		{
			// units are optional
			unitsConcept = f.createConcept(getIdForConcept(measurement.getUnits().getConcept()));
		}

		IConcept data;
		if (measurement.getPoint() != null)
		{
			Point p = measurement.getPoint();
			data = processPoint(feature, p, Operator.EQUALS);
		}
		else if (measurement.getBound() != null)
		{
			Bound b = measurement.getBound();

			IConcept lower = null;
			IConcept upper = null;
			if (b.getLowerPoint() != null)
			{
				Operator lowerOperator = null;
				if (b.isLowerPointInclusive() == null || b.isLowerPointInclusive())
				{
					lowerOperator = Operator.GREATER_THAN_EQUALS;
				}
				else
				{
					lowerOperator = Operator.GREATER_THAN;
				}
				lower = processPoint(feature, b.getLowerPoint(), lowerOperator);
			}

			if (b.getUpperPoint() != null)
			{
				Operator upperOperator = null;
				if (b.isUpperPointInclusive() == null || b.isUpperPointInclusive())
				{
					upperOperator = Operator.LESS_THAN_EQUALS;
				}
				else
				{
					upperOperator = Operator.LESS_THAN;
				}
				upper = processPoint(feature, b.getUpperPoint(), upperOperator);
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
		else if (measurement.getInterval() != null)
		{
			Interval i = measurement.getInterval();

			// In the case of bounds, where we have an uncertainty range on each end of the interval - like this:
			// {[5] to (8)} <= X <= {(20) to [30]}
			// We turn this into [5] <= X <= [30] - as the classifier doesn't have a way to distinguish between definitely in the bound, and possibly
			// in the bound.
			// This will only allow querying if a point is in the interval but it will be impossible to know if it is either possibly
			// in the interval or definitively in the interval

			IConcept lower = null;
			IConcept upper = null;
			if (i.getLowerBound() != null && i.getLowerBound().getLowerPoint() != null)
			{
				Operator lowerOperator = null;
				if (i.getLowerBound().isLowerPointInclusive() == null || i.getLowerBound().isLowerPointInclusive())
				{
					lowerOperator = Operator.GREATER_THAN_EQUALS;
				}
				else
				{
					lowerOperator = Operator.GREATER_THAN;
				}
				lower = processPoint(feature, i.getLowerBound().getLowerPoint(), lowerOperator);
			}

			if (i.getUpperBound() != null && i.getUpperBound().getUpperPoint() != null)
			{
				Operator upperOperator = null;
				if (i.getUpperBound().isUpperPointInclusive() == null || i.getUpperBound().isUpperPointInclusive())
				{
					upperOperator = Operator.LESS_THAN_EQUALS;
				}
				else
				{
					upperOperator = Operator.LESS_THAN;
				}
				upper = processPoint(feature, i.getUpperBound().getUpperPoint(), upperOperator);
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
			throw new RuntimeException("invalid measurement");
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

	/**
	 * @param lowerPoint - null to say neither lower nor upper (just a point), true for lower, false for upper
	 * @return
	 */
	private IConcept processPoint(INamedFeature<String> feature, Point point, Operator operator)
	{
		if (point instanceof PointLong)
		{
			ILiteral literal = f.createLongLiteral(((PointLong) point).getValue());
			return f.createDatatype(feature, operator, literal);
		}
		else if (point instanceof PointDouble)
		{
			ILiteral literal = f.createDoubleLiteral(((PointDouble) point).getValue());
			return f.createDatatype(feature, operator, literal);
		}
		else if (point instanceof PointMeasurementConstant)
		{
			ILiteral literal = f.createStringLiteral(((PointMeasurementConstant) point).getValue().name());
			return f.createDatatype(feature, operator, literal);
		}
		else
		{
			throw new RuntimeException("invalid point");
		}
	}

	private IConcept processRelationship(Relation r)
	{
		// We need to determine if this relation refers to a role or a feature.
		// This is done by looking at the destination.
		Destination dest = r.getDestination();
		Type tp = r.getType();

		if (dest.getExpression() != null)
		{
			// If the destination is an expression the type is role
			INamedRole<String> role = f.createRole(getIdForConcept(tp.getConcept()));
			IConcept destExpression = process(dest.getExpression());
			return f.createExistential(role, destExpression);
		}
		else if (dest.getMeasurement() != null)
		{
			INamedFeature<String> feature = f.createFeature(getIdForConcept(tp.getConcept()));
			IConcept measurementConcept = processMeasurement(feature, dest.getMeasurement());
			return measurementConcept;
		}
		else if (dest.getText() != null && r.getDestination().getText().length() > 0)
		{
			INamedFeature<String> feature = f.createFeature(getIdForConcept(tp.getConcept()));
			ILiteral literal = f.createStringLiteral(dest.getText());
			IConcept data = f.createDatatype(feature, Operator.EQUALS, literal);
			return data;
		}
		else if (dest.isBoolean() != null)
		{
			INamedFeature<String> feature = f.createFeature(getIdForConcept(tp.getConcept()));
			ILiteral literal = f.createBooleanLiteral(dest.isBoolean());
			IConcept data = f.createDatatype(feature, Operator.EQUALS, literal);
			return data;
		}
		else
		{
			throw new RuntimeException("invalid rel");
		}
	}

	/**
	 * Generate a unique ID based off of the expressions (and all subconcepts)
	 */
	// TODO all of these generate functions need to be reworked so that they generate an ID that doesn't change if the order of the children changes
	//Note - the IDs generated here will not be consistent with the IDs generated by the SIM-API.
	private String generateUUID(Expression expression)
	{
		// Note, this only gets called for conjunction expressions...
		StringBuilder sb = new StringBuilder();
		buildIDComponents(sb, expression);
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
			sb.append(getIdForConcept(expression.getConcept()));
		}
		else if (expression.getExpression().size() > 0)
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
			//I don't think roleGroups need to be identified to the classifier.
			for (RelationGroup rg : expression.getRelationGroup())
			{
				for (Relation r : rg.getRelation())
				{
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
		String id = null;
		if (c.getUuid() != null && c.getUuid().length() > 0)
		{
			id = c.getUuid();
		}
		else if (c.getSctid() != null)
		{
			// This is how snomed UUIDs are calculated
			try
			{
				id = UUID.nameUUIDFromBytes(("org.snomed." + c.getSctid().toString()).getBytes("8859_1")).toString();
			}
			catch (UnsupportedEncodingException e)
			{
				throw new RuntimeException(e);
			}
		}
		else
		{
			throw new IllegalArgumentException("No ID found for concept " + c.getDesc());
		}

		// should be impossible, but just to be safe...
		if (id == null)
		{
			throw new RuntimeException("oops");
		}
		conceptIds.add(id);
		return id;
	}

	private String getValuesInInterval(Interval i)
	{
		if (i == null)
		{
			return "";
		}
		else
		{
			return getValuesInBound(i.getLowerBound()) + getValuesInBound(i.getUpperBound());
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
			return getValueInPoint(b.getLowerPoint()) + getValueInPoint(b.getUpperPoint()) + ":" + b.isLowerPointInclusive() + ":" + b.isUpperPointInclusive();
		}
	}

	private String getValueInPoint(Point p)
	{
		if (p == null)
		{
			return "";
		}
		else if (p instanceof PointLong)
		{
			return ":" + ((PointLong) p).getValue();
		}
		else if (p instanceof PointDouble)
		{
			return ":" + ((PointDouble) p).getValue();
		}
		else if (p instanceof PointMeasurementConstant)
		{
			return ":" + ((PointMeasurementConstant) p).getValue().name();
		}
		else
		{
			throw new InvalidParameterException();
		}
	}

	/**
	 * @param args
	 */
	public static void main(String[] args)
	{
		ArrayList<Lego> legos = new ArrayList<Lego>();
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
						legos.add(l);
					}

				}
				catch (Exception ex)
				{
					logger.error("Error reading file " + f.getName(), ex);
				}
			}
		}

		LegoClassifier lc = new LegoClassifier(new SnorocketReasoner<String>());
		lc.convertToAxioms(legos.toArray(new Lego[legos.size()]));

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
