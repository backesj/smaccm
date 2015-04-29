#ifndef __SMACCM_can_node_types__H
#define __SMACCM_can_node_types__H

#include <smaccm_wrapper_i_types.h>

/**************************************************************************
  Copyright (c) 2013, 2014, 2015 Rockwell Collins and the University of Minnesota.
  Developed with the sponsorship of the Defense Advanced Research Projects Agency (DARPA).

  Permission is hereby granted, free of charge, to any person obtaining a copy of this data,
  including any software or models in source or binary form, as well as any drawings, specifications, 
  and documentation (collectively "the Data"), to deal in the Data without restriction, including 
  without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, 
  and/or sell copies of the Data, and to permit persons to whom the Data is furnished to do so, 
  subject to the following conditions: 

  The above copyright notice and this permission notice shall be included in all copies or
  substantial portions of the Data.

  THE DATA IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT 
  LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. 
  IN NO EVENT SHALL THE AUTHORS, SPONSORS, DEVELOPERS, CONTRIBUTORS, OR COPYRIGHT HOLDERS BE LIABLE 
  FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, 
  ARISING FROM, OUT OF OR IN CONNECTION WITH THE DATA OR THE USE OR OTHER DEALINGS IN THE DATA. 

 **************************************************************************/


/**************************************************************************

   File: /home/ajgacek/smaccm/models/Trusted_Build_Test/can/components/can_node/include/smaccm_can_node.h
   Created on: 2015/04/23 16:39:39
   using Dulcimer AADL system build tool suite 

   ***AUTOGENERATED CODE: DO NOT MODIFY***

  This header section contains the AADL gluecode interfaces used by the client
  for the thread implementations.

 **************************************************************************/
	bool can_node_write_client_output(const can__can_frame_i * client_output); 
	bool can_node_read_client_input(can__can_frame_i * client_input); 
		//////////////////////////////////////////////////////////////////////////
		// 
		// Note: thread is declared EXTERNAL; user should provide run() function.
		//
		//////////////////////////////////////////////////////////////////////////
	
/* endif for: #ifndef __SMACCM_can_node_types__H */
#endif

/**************************************************************************
  End of autogenerated file: /home/ajgacek/smaccm/models/Trusted_Build_Test/can/components/can_node/include/smaccm_can_node.h
 **************************************************************************/
