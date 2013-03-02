package gov.va;

import static org.junit.Assert.assertEquals;
import gov.va.legoEdit.formats.LegoXMLUtils;
import gov.va.legoEdit.model.schemaModel.Lego;
import gov.va.legoEdit.model.schemaModel.LegoList;
import java.io.IOException;
import java.util.ArrayList;
import javax.xml.bind.JAXBException;
import org.junit.Test;
import org.xml.sax.SAXException;
import au.csiro.ontology.classification.IReasoner;
import au.csiro.snorocket.core.SnorocketReasoner;

/**
 * Note - the things that are being tested in this class are basically:
 * Nothing crashes
 * The tested counts are the same as when I implemented the test.
 * The actual truth values are unknown to me, so this isn't a truth test.
 * 
 * @author darmbrust
 */
public class SnomedClassifyTest
{
	@Test
	public void testSnomedClassify() throws IOException, SAXException, JAXBException
	{
		ArrayList<Lego> legos = new ArrayList<Lego>();
		LegoList ll = LegoXMLUtils.readLegoList(this.getClass().getResourceAsStream("/Pressure ulcer observables.xml"));
		for (Lego l : ll.getLego())
		{
			legos.add(l);
		}

		@SuppressWarnings("unchecked") 
		IReasoner<String> reasoner = SnorocketReasoner.load(this.getClass().getResourceAsStream("/classifier_uuid.state"));

		LegoClassifier lc = new LegoClassifier(reasoner);
		lc.convertToAxioms(legos.toArray(new Lego[legos.size()]));

		assertEquals("Wrong number of Axioms", 2, lc.getUnclassifiedAxioms().size());

		assertEquals("unexpected node count before classification", 397320, reasoner.getClassifiedOntology().getNodeMap().size());

		lc.classifyAxioms();

		assertEquals("unexpected node count after classification", 397322, reasoner.getClassifiedOntology().getNodeMap().size());
	}
}
