package edu.mit.csail.sdg.alloy4whole;

public class AlloyLSMessage {
	public AlloyLSMessageType messageType;
	public String message;
	public String link;
	
	public boolean bold;
	public boolean replaceLast;
	public boolean lineBreak = true;
	
	public AlloyLSMessage(AlloyLSMessageType messageType, String message, String link) {
		this.messageType = messageType;
		this.message = message;
		this.link = link;
	}
	
	public AlloyLSMessage(AlloyLSMessageType messageType, String message) {
		this(messageType, message, null);
	}
	
}

enum AlloyLSMessageType{
	RunStarted,
	RunInProgress,
	RunResult,
	RunCompleted,
	Warning
}