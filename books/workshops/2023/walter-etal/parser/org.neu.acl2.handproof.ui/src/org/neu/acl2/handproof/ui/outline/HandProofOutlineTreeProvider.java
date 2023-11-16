/*
 * generated by Xtext 2.20.0
 */
package org.neu.acl2.handproof.ui.outline;

import java.util.List;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.ui.editor.outline.IOutlineNode;
import org.eclipse.xtext.ui.editor.outline.impl.DefaultOutlineTreeProvider;
import org.eclipse.xtext.ui.editor.outline.impl.DocumentRootNode;
import org.neu.acl2.handproof.handProof.Context;
import org.neu.acl2.handproof.handProof.ContractCompletionSection;
import org.neu.acl2.handproof.handProof.DefineC;
import org.neu.acl2.handproof.handProof.DefunC;
import org.neu.acl2.handproof.handProof.DerivedContext;
import org.neu.acl2.handproof.handProof.ExportationSection;
import org.neu.acl2.handproof.handProof.HintList;
import org.neu.acl2.handproof.handProof.Proof;
import org.neu.acl2.handproof.handProof.ProofBody;
import org.neu.acl2.handproof.handProof.ProofDocument;
import org.neu.acl2.handproof.handProof.SExpression;
import org.neu.acl2.handproof.handProof.TermProofCase;
import org.neu.acl2.handproof.handProof.TerminationProof;
import org.neu.acl2.handproof.handProof.contextItem;
import org.neu.acl2.handproof.handProof.dcontextItem;

/**
 * Customization of the default outline structure.
 *
 * See https://www.eclipse.org/Xtext/documentation/310_eclipse_support.html#outline
 */
public class HandProofOutlineTreeProvider extends DefaultOutlineTreeProvider {
	protected void _createChildren(IOutlineNode parentNode, Context context) {
		context.getContext().forEach(item -> createNode(parentNode, item));
	}
	
	protected void _createChildren(IOutlineNode parentNode, DerivedContext context) {
		context.getDerivedContext().forEach(item -> createNode(parentNode, item));
	}
	
	protected void _createChildren(IOutlineNode parentNode, Proof proof) {
		createNode(parentNode, proof.getStatement());
		if(proof.getExportation() != null) createNode(parentNode, proof.getExportation());
		if(proof.getCompletion() != null) createNode(parentNode, proof.getCompletion());
		if(proof.getContext() != null && ((List<contextItem>) proof.getContext().getContext()).size() > 0) createNode(parentNode, proof.getContext());
		if(proof.getDerivedContext() != null && ((List<dcontextItem>) proof.getDerivedContext().getDerivedContext()).size() > 0) createNode(parentNode, proof.getDerivedContext());
		if(proof.getGoal() != null) createNode(parentNode, proof.getGoal());
		if(proof.getBody() != null) createNode(parentNode, proof.getBody());
	}
	
	protected void _createChildren(IOutlineNode parentNode, TerminationProof proof) {
		createNode(parentNode, proof.getHead());
		for(EObject d : proof.getDefinitions()) {
			createNode(parentNode, d);
		}
		for(EObject term_case : proof.getCases()) {
			createNode(parentNode, ((TermProofCase) term_case).getHead());
		}
	}
	
	protected void _createChildren(IOutlineNode parentNode, ProofBody body) {
		body.getHints().stream().forEach(item -> createNode(parentNode, item));
	}
	
//	protected void _createChildren(IOutlineNode parentNode, ProofBody body) {
//		body.getHints().stream().forEach(item -> createNode(parentNode, item));
//	}
	
	protected void _createNode(DocumentRootNode parentNode, ProofDocument doc) {
		doc.getProofsAndStatements().stream()
//			.filter(item -> (item instanceof Proof || item instanceof DefineC || item instanceof TerminationProof || item instanceof DefunC))
			.forEach(item -> createNode(parentNode, item));
	}
	
	protected void _createChildren(IOutlineNode parentNode, DefineC definition) {
		createNode(parentNode, definition);
	}
	
	protected void _createChildren(IOutlineNode parentNode, DefunC definition) {
		createNode(parentNode, definition);
	}
	
	protected boolean _isLeaf(TermProofCase tpc) {
		return true;
	}
	
	protected boolean _isLeaf(DefineC def) {
		return true;
	}
	
	protected boolean _isLeaf(DefunC def) {
		return true;
	}
	
	protected boolean _isLeaf(SExpression sexp) {
		return true;
	}
	
	protected boolean _isLeaf(contextItem item) {
		return true;
	}
	
	protected boolean _isLeaf(dcontextItem item) {
		return true;
	}
	
	protected boolean _isLeaf(ProofBody body) {
		return false;
	}
	
	protected boolean _isLeaf(HintList hl) {
		return true;
	}
	
//	protected boolean _isLeaf(ExportationSection es) {
//		return true;
//	}
//	
//	protected boolean _isLeaf(ContractCompletionSection ccs) {
//		return true;
//	}
}
