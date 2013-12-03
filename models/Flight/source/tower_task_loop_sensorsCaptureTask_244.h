/* This file has been autogenerated by Ivory
 * Compiler version  0.1.0.0
 */
#ifndef __TOWER_TASK_LOOP_SENSORSCAPTURETASK_244_H__
#define __TOWER_TASK_LOOP_SENSORSCAPTURETASK_244_H__
#ifdef __cplusplus
extern "C" {
#endif
#include "controloutput_type.h"
#include "data_rate.h"
#include "flightmode_type.h"
#include "gcsstream_timing.h"
#include "gps_type.h"
#include "ivory.h"
#include "mavlink_hil_state_msg.h"
#include "motors_type.h"
#include "optflow_type.h"
#include "radio_info_type.h"
#include "radio_stat_type.h"
#include "sensors_type.h"
#include "tower_primitives.h"
#include "tower_task_usercode_sensorsCaptureTask_244.h"
#include "userinput_type.h"
bool emitFromTask_sensorsCaptureTask_244_chan0_246(const
                                                   struct sensors_result* n_var0);
bool receiveFromTask_sensorsCaptureTask_244_chan216_249(struct position* n_var0);
bool emitFromTask_sensorsCaptureTask_244_chan257_259(const uint32_t* n_var0);
bool receiveFromTask_sensorsCaptureTask_244_chan257_261(uint32_t* n_var0);

#ifdef __cplusplus
}
#endif
#endif /* __TOWER_TASK_LOOP_SENSORSCAPTURETASK_244_H__ */