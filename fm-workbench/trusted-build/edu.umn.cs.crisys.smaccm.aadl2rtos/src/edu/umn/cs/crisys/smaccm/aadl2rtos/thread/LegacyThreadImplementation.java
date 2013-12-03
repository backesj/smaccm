package edu.umn.cs.crisys.smaccm.aadl2rtos.thread;

/**
 * @author Mead, Whalen
 * 
 * TODO:    In "ThreadImplementation"
 *    ! FIXED: only one thread instance for thread implementation (should be list)
 *    -> ISR threads are not distinguished from "regular" threads
 * 
 */

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.osate.aadl2.EnumerationLiteral;
import org.osate.aadl2.impl.ThreadTypeImpl;
import org.osate.xtext.aadl2.properties.util.PropertyUtils;

import edu.umn.cs.crisys.smaccm.aadl2rtos.Aadl2RtosException;
import edu.umn.cs.crisys.smaccm.aadl2rtos.AstHelper;
import edu.umn.cs.crisys.smaccm.aadl2rtos.util.ThreadUtil;
import edu.umn.cs.crisys.smaccm.aadl2rtos.util.Util;

public class LegacyThreadImplementation extends ThreadImplementationBase {

	// Data port lists
	private ArrayList<String> legacySemaphoreList = new ArrayList<String>();
	/*
	 * 		// Determine whether this is a legacy ("blob") thread
		legacyThread = ThreadUtil.getLegacyValue(tti);
		if (legacyThread) {
			legacySemaphoreList = (ArrayList<String>) ThreadUtil.getLegacySemaphoreList(tti);
		}

	 */
	// Constructor
	public LegacyThreadImplementation(ThreadTypeImpl tti, AstHelper astHelper)  
	{
		super(tti, astHelper);
		try { 
			legacySemaphoreList = (ArrayList<String>) ThreadUtil.getLegacySemaphoreList(tti);
			generatedEntrypoint = Util.getStringValue(tti, ThreadUtil.LEGACY_ENTRYPOINT);
		} catch (Exception e) {
			throw new Aadl2RtosException("Error: Legacy threads must have a SMACCM_SYS::Legacy_Entrypoint property defined");
		}
	}
	
	public boolean isLegacyThread() {
		return true;
	}

	public List<String> getLegacySemaphores() {
	    return this.legacySemaphoreList;
	}
	  
}