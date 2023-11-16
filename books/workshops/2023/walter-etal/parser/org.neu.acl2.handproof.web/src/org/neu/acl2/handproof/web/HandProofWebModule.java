/*
 * generated by Xtext 2.26.0
 */
package org.neu.acl2.handproof.web;

import org.eclipse.xtext.web.server.XtextServiceDispatcher;
import org.eclipse.xtext.web.server.validation.ValidationService;

/**
 * Use this class to register additional components to be used within the web application.
 */
public class HandProofWebModule extends AbstractHandProofWebModule {
    public Class<? extends ValidationService> bindValidationService() {
        return MyValidationService.class;
    }

    public Class<? extends XtextServiceDispatcher> bindXtextServiceDispatcher() {
        return MyXtextServiceDispatcher.class;
    }
}
